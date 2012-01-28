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

#define SAT_USE_PROOF_LOGGING

//=================================================================================================
// Debug:

//#define VERBOSEDEBUG

// For derivation output (verbosity level 2)
#define L_IND    "%-*d"
#define L_ind    solver2_dlevel(s)*2+2,solver2_dlevel(s)
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
// Variable datatype + minor functions:

static const int var0  = 1;
static const int var1  = 0;
static const int varX  = 3;

struct varinfo2_t
{
//    unsigned val    :  2;  // variable value 
    unsigned pol    :  1;  // last polarity
    unsigned partA  :  1;  // partA variable
    unsigned tag    :  4;  // conflict analysis tags
//    unsigned lev    : 24;  // variable level
};

int    var_is_partA (sat_solver2* s, int v)              { return s->vi[v].partA;  }
void   var_set_partA(sat_solver2* s, int v, int partA)   { s->vi[v].partA = partA; }

//static inline int     var_level     (sat_solver2* s, int v)            { return s->vi[v].lev; }
static inline int     var_level     (sat_solver2* s, int v)            { return s->levels[v];  }
//static inline int     var_value     (sat_solver2* s, int v)            { return s->vi[v].val; }
static inline int     var_value     (sat_solver2* s, int v)            { return s->assigns[v]; }
static inline int     var_polar     (sat_solver2* s, int v)            { return s->vi[v].pol; }

//static inline void    var_set_level (sat_solver2* s, int v, int lev)   { s->vi[v].lev = lev;  }
static inline void    var_set_level (sat_solver2* s, int v, int lev)   { s->levels[v] = lev;  }
//static inline void    var_set_value (sat_solver2* s, int v, int val)   { s->vi[v].val = val;  }
static inline void    var_set_value (sat_solver2* s, int v, int val)   { s->assigns[v] = val; }
static inline void    var_set_polar (sat_solver2* s, int v, int pol)   { s->vi[v].pol = pol;  }

// variable tags
static inline int     var_tag       (sat_solver2* s, int v)            { return s->vi[v].tag; }
static inline void    var_set_tag   (sat_solver2* s, int v, int tag)   { 
    assert( tag > 0 && tag < 16 );
    if ( s->vi[v].tag == 0 )
        veci_push( &s->tagged, v );
    s->vi[v].tag = tag;                           
}
static inline void    var_add_tag   (sat_solver2* s, int v, int tag)   { 
    assert( tag > 0 && tag < 16 );
    if ( s->vi[v].tag == 0 )
        veci_push( &s->tagged, v );
    s->vi[v].tag |= tag;                           
}
static inline void    solver2_clear_tags(sat_solver2* s, int start)    { 
    int i, * tagged = veci_begin(&s->tagged);
    for (i = start; i < veci_size(&s->tagged); i++)
        s->vi[tagged[i]].tag = 0;
    veci_resize(&s->tagged,start);
}

// level marks
static inline int     var_lev_mark (sat_solver2* s, int v)             { 
    return (veci_begin(&s->trail_lim)[var_level(s,v)] & 0x80000000) > 0;   
}
static inline void    var_lev_set_mark (sat_solver2* s, int v)         { 
    int level = var_level(s,v);
    assert( level < veci_size(&s->trail_lim) );
    veci_begin(&s->trail_lim)[level] |= 0x80000000;
    veci_push(&s->mark_levels, level);
}
static inline void    solver2_clear_marks(sat_solver2* s)              { 
    int i, * mark_levels = veci_begin(&s->mark_levels);
    for (i = 0; i < veci_size(&s->mark_levels); i++)
        veci_begin(&s->trail_lim)[mark_levels[i]] &= 0x7FFFFFFF;
    veci_resize(&s->mark_levels,0);
}

//=================================================================================================
// Clause datatype + minor functions:

static inline satset* clause_read   (sat_solver2* s, cla h)      { return (h & 1) ? satset_read(&s->learnts, h>>1)  : satset_read(&s->clauses, h>>1);          }
static inline cla     clause_handle (sat_solver2* s, satset* c)  { return c->learnt ? (satset_handle(&s->learnts, c)<<1)|1: satset_handle(&s->clauses, c)<<1;  }
static inline int     clause_check  (sat_solver2* s, satset* c)  { return c->learnt ? satset_check(&s->learnts, c)  : satset_check(&s->clauses, c);            }
static inline int     clause_proofid(sat_solver2* s, satset* c, int partA)  { return c->learnt ? (veci_begin(&s->claProofs)[c->Id]<<2) | (partA<<1) : (satset_handle(&s->clauses, c)<<2) | (partA<<1) | 1; }
static inline int     clause_is_used(sat_solver2* s, cla h)      { return (h & 1) ? ((h >> 1) < s->hLearntPivot) : ((h >> 1) < s->hClausePivot);               }

//static inline int     var_reason    (sat_solver2* s, int v)      { return (s->reasons[v]&1) ? 0 : s->reasons[v] >> 1;                   } 
//static inline int     lit_reason    (sat_solver2* s, int l)      { return (s->reasons[lit_var(l)&1]) ? 0 : s->reasons[lit_var(l)] >> 1; } 
//static inline satset* var_unit_clause(sat_solver2* s, int v)           { return (s->reasons[v]&1) ? clause_read(s, s->reasons[v] >> 1) : NULL;  } 
//static inline void    var_set_unit_clause(sat_solver2* s, int v, cla i){ assert(i && !s->reasons[v]); s->reasons[v] = (i << 1) | 1;             } 
static inline int     var_reason    (sat_solver2* s, int v)            { return s->reasons[v];           } 
static inline int     lit_reason    (sat_solver2* s, int l)            { return s->reasons[lit_var(l)];  } 
static inline satset* var_unit_clause(sat_solver2* s, int v)           { return clause_read(s, s->units[v]);                                          } 
static inline void    var_set_unit_clause(sat_solver2* s, int v, cla i){ 
    assert(v >= 0 && v < s->size && !s->units[v]); s->units[v] = i; s->nUnits++; 
} 
//static inline void    var_set_unit_clause(sat_solver2* s, int v, cla i){ assert(v >= 0 && v < s->size); s->units[v] = i; s->nUnits++; } 

// these two only work after creating a clause before the solver is called
int    clause_is_partA (sat_solver2* s, int h)                   { return clause_read(s, h)->partA;         }  
void   clause_set_partA(sat_solver2* s, int h, int partA)        { clause_read(s, h)->partA = partA;        }
int    clause_id(sat_solver2* s, int h)                          { return clause_read(s, h)->Id;            }

//=================================================================================================
// Simple helpers:

static inline int     solver2_dlevel(sat_solver2* s)       { return veci_size(&s->trail_lim); }
static inline veci*   solver2_wlist(sat_solver2* s, lit l) { return &s->wlists[l];            }

//=================================================================================================
// Proof logging:

static inline void proof_chain_start( sat_solver2* s, satset* c )
{
    if ( s->fProofLogging )
    {
        s->iStartChain = veci_size(&s->proofs);
        veci_push(&s->proofs, 0);
        veci_push(&s->proofs, 0);
        veci_push(&s->proofs, clause_proofid(s, c, 0) );
    }
}

static inline void proof_chain_resolve( sat_solver2* s, satset* cls, int Var )
{
    if ( s->fProofLogging )
    {
        satset* c = cls ? cls : var_unit_clause( s, Var );
        veci_push(&s->proofs, clause_proofid(s, c, var_is_partA(s,Var)) );
//        printf( "%d %d  ", clause_proofid(s, c), Var );
    }
}

static inline int proof_chain_stop( sat_solver2* s )
{
    if ( s->fProofLogging )
    {
        int RetValue = s->iStartChain;
        satset* c = (satset*)(veci_begin(&s->proofs) + s->iStartChain);
        assert( s->iStartChain > 0 && s->iStartChain < veci_size(&s->proofs) );
        c->nEnts = veci_size(&s->proofs) - s->iStartChain - 2;
        s->iStartChain = 0;
        return RetValue;
    }
    return 0;
}

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
        if (var_value(s, next) == varX)
            return next;
    }
    return var_Undef;
}


//=================================================================================================
// Activity functions:

#ifdef USE_FLOAT_ACTIVITY2

static inline void act_var_rescale(sat_solver2* s)  {
    double* activity = s->activity;
    int i;
    for (i = 0; i < s->size; i++)
        activity[i] *= 1e-100;
    s->var_inc *= 1e-100;
}
static inline void act_clause_rescale(sat_solver2* s) {
    static int Total = 0;
    float * claActs = (float *)veci_begin(&s->claActs);
    int i, clk = clock();
    for (i = 0; i < veci_size(&s->claActs); i++)
        claActs[i] *= (float)1e-20;
    s->cla_inc *= (float)1e-20;

    Total += clock() - clk;
    printf( "Rescaling...   Cla inc = %10.3f  Conf = %10d   ", s->cla_inc,  s->stats.conflicts );
    Abc_PrintTime( 1, "Time", Total );
}
static inline void act_var_bump(sat_solver2* s, int v) {
    s->activity[v] += s->var_inc;
    if (s->activity[v] > 1e100)
        act_var_rescale(s);
    if (s->orderpos[v] != -1)
        order_update(s,v);
}
static inline void act_clause_bump(sat_solver2* s, satset*c) {
    float * claActs = (float *)veci_begin(&s->claActs);
    assert( c->Id < veci_size(&s->claActs) );
    claActs[c->Id] += s->cla_inc;
    if (claActs[c->Id] > (float)1e20) 
        act_clause_rescale(s);
}
static inline void act_var_decay(sat_solver2* s)    { s->var_inc *= s->var_decay; }
static inline void act_clause_decay(sat_solver2* s) { s->cla_inc *= s->cla_decay; }

#else

static inline void act_var_rescale(sat_solver2* s) {
    unsigned* activity = s->activity;
    int i;
    for (i = 0; i < s->size; i++)
        activity[i] >>= 19;
    s->var_inc >>= 19;
    s->var_inc = Abc_MaxInt( s->var_inc, (1<<4) );
}
static inline void act_clause_rescale(sat_solver2* s) {
    static int Total = 0;
    int i, clk = clock();
    unsigned * claActs = (unsigned *)veci_begin(&s->claActs);
    for (i = 1; i < veci_size(&s->claActs); i++)
        claActs[i] >>= 14;
    s->cla_inc >>= 14;
    s->cla_inc = Abc_MaxInt( s->cla_inc, (1<<10) );

//    Total += clock() - clk;
//    printf( "Rescaling...   Cla inc = %5d  Conf = %10d   ", s->cla_inc,  s->stats.conflicts );
//    Abc_PrintTime( 1, "Time", Total );
}
static inline void act_var_bump(sat_solver2* s, int v) {
    s->activity[v] += s->var_inc;
    if (s->activity[v] & 0x80000000)
        act_var_rescale(s);
    if (s->orderpos[v] != -1)
        order_update(s,v);
}
static inline void act_clause_bump(sat_solver2* s, satset*c) {
    unsigned * claActs = (unsigned *)veci_begin(&s->claActs);
    assert( c->Id > 0 && c->Id < veci_size(&s->claActs) );
    claActs[c->Id] += s->cla_inc;
    if (claActs[c->Id] & 0x80000000) 
        act_clause_rescale(s);
}
static inline void act_var_decay(sat_solver2* s)    { s->var_inc += (s->var_inc >>  4); }
static inline void act_clause_decay(sat_solver2* s) { s->cla_inc += (s->cla_inc >> 10); }

#endif

//=================================================================================================
// Clause functions:

static int clause_create_new(sat_solver2* s, lit* begin, lit* end, int learnt, int proof_id)
{
    satset* c;
    int i, Cid, nLits = end - begin;
    assert(nLits < 1 || begin[0] >= 0);
    assert(nLits < 2 || begin[1] >= 0);
    assert(nLits < 1 || lit_var(begin[0]) < s->size);
    assert(nLits < 2 || lit_var(begin[1]) < s->size);
    // add memory if needed

    // assign clause ID
    if ( learnt )
    {
        if ( veci_size(&s->learnts) + satset_size(nLits) > s->learnts.cap )
        {
            int nMemAlloc = s->learnts.cap ? 2 * s->learnts.cap : (1 << 20);
            s->learnts.ptr = ABC_REALLOC( int, veci_begin(&s->learnts), nMemAlloc );
    //        printf( "Reallocing from %d to %d...\n", s->learnts.cap, nMemAlloc );
            s->learnts.cap = nMemAlloc;
            if ( veci_size(&s->learnts) == 0 )
                veci_push( &s->learnts, -1 );
        }
        // create clause
        c = (satset*)(veci_begin(&s->learnts) + veci_size(&s->learnts));
        ((int*)c)[0] = 0;
        c->learnt = learnt;
        c->nEnts  = nLits;
        for (i = 0; i < nLits; i++)
            c->pEnts[i] = begin[i];
        // count the clause
        s->stats.learnts++;
        s->stats.learnts_literals += nLits;
        c->Id = s->stats.learnts;
        assert( c->Id == veci_size(&s->claActs) );
        veci_push(&s->claActs, 0);
        if ( proof_id )
            veci_push(&s->claProofs, proof_id);
        if ( nLits > 2 )
            act_clause_bump( s,c );
        // extend storage
        Cid = (veci_size(&s->learnts) << 1) | 1;
        s->learnts.size += satset_size(nLits);
        assert( veci_size(&s->learnts) <= s->learnts.cap );
        assert(((ABC_PTRUINT_T)c & 3) == 0);
//        printf( "Clause for proof %d: ", proof_id );
//        satset_print( c );
        // remember the last one
        s->hLearntLast = Cid;
    }
    else
    {
        if ( veci_size(&s->clauses) + satset_size(nLits) > s->clauses.cap )
        {
            int nMemAlloc = s->clauses.cap ? 2 * s->clauses.cap : (1 << 20);
            s->clauses.ptr = ABC_REALLOC( int, veci_begin(&s->clauses), nMemAlloc );
    //        printf( "Reallocing from %d to %d...\n", s->clauses.cap, nMemAlloc );
            s->clauses.cap = nMemAlloc;
            if ( veci_size(&s->clauses) == 0 )
                veci_push( &s->clauses, -1 );
        }
        // create clause
        c = (satset*)(veci_begin(&s->clauses) + veci_size(&s->clauses));
        ((int*)c)[0] = 0;
        c->learnt = learnt;
        c->nEnts  = nLits;
        for (i = 0; i < nLits; i++)
            c->pEnts[i] = begin[i];
        // count the clause
        s->stats.clauses++;
        s->stats.clauses_literals += nLits;
        c->Id = s->stats.clauses;
        // extend storage
        Cid = (veci_size(&s->clauses) << 1);
        s->clauses.size += satset_size(nLits);
        assert( veci_size(&s->clauses) <= s->clauses.cap );
        assert(((ABC_PTRUINT_T)c & 3) == 0);
    }
    // watch the clause
    if ( nLits > 1 ){
        veci_push(solver2_wlist(s,lit_neg(begin[0])),Cid);
        veci_push(solver2_wlist(s,lit_neg(begin[1])),Cid);
    }
    return Cid;
}

//=================================================================================================
// Minor (solver) functions:

static inline int solver2_enqueue(sat_solver2* s, lit l, cla from)
{
    int v = lit_var(l);
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
        var_set_level( s, v, solver2_dlevel(s) );
        s->reasons[v] = from;  //  = from << 1;
        s->trail[s->qtail++] = l;
        order_assigned(s, v);
/*
        if ( solver2_dlevel(s) == 0 )
        {
            satset * c = from ? clause_read( s, from ) : NULL;
            printf( "Enqueing var %d on level %d with reason clause  ", v, solver2_dlevel(s) );
            if ( c )
                satset_print( c );
            else
                printf( "<none>\n" );           
        }
*/
        return true;
    }
}

static inline int solver2_assume(sat_solver2* s, lit l)
{
    assert(s->qtail == s->qhead);
    assert(var_value(s, lit_var(l)) == varX);
#ifdef VERBOSEDEBUG
    printf(L_IND"assume("L_LIT")  ", L_ind, L_lit(l));
    printf( "act = %.20f\n", s->activity[lit_var(l)] );
#endif
    veci_push(&s->trail_lim,s->qtail);
    return solver2_enqueue(s,l,0);
}

static void solver2_canceluntil(sat_solver2* s, int level) {
    lit*     trail;   
    int      bound;
    int      lastLev;
    int      c, x;
   
    if (solver2_dlevel(s) < level)
        return;

    trail   = s->trail;
    bound   = (veci_begin(&s->trail_lim))[level];
    lastLev = (veci_begin(&s->trail_lim))[veci_size(&s->trail_lim)-1];

    for (c = s->qtail-1; c >= bound; c--) 
    {
        x = lit_var(trail[c]);
        var_set_value(s, x, varX);
        s->reasons[x] = 0;
        s->units[x] = 0; // temporary?
        if ( c < lastLev )
            var_set_polar(s, x, !lit_sign(trail[c]));
    }

    for (c = s->qhead-1; c >= bound; c--)
        order_unassigned(s,lit_var(trail[c]));

    s->qhead = s->qtail = bound;
    veci_resize(&s->trail_lim,level);
}


static void solver2_record(sat_solver2* s, veci* cls, int proof_id)
{
    lit* begin = veci_begin(cls);
    lit* end   = begin + veci_size(cls);
    cla  Cid   = clause_create_new(s,begin,end,1, proof_id);
    assert(veci_size(cls) > 0);
    if ( veci_size(cls) == 1 )
    {
        if ( s->fProofLogging )
            var_set_unit_clause(s, lit_var(begin[0]), Cid);
        Cid = 0;
    }
    solver2_enqueue(s, begin[0], Cid);
}


static double solver2_progress(sat_solver2* s)
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
void Solver::analyzeFinal(satset* confl, bool skip_first)
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

static int solver2_analyze_final(sat_solver2* s, satset* conf, int skip_first)
{
    int i, j, x;//, start;
    veci_resize(&s->conf_final,0);
    if ( s->root_level == 0 )
        return s->hProofLast;
    proof_chain_start( s, conf );
    assert( veci_size(&s->tagged) == 0 );
    satset_foreach_var( conf, x, i, skip_first ){
        if ( var_level(s,x) )
            var_set_tag(s, x, 1);
        else
            proof_chain_resolve( s, NULL, x );
    }
    assert( s->root_level >= veci_size(&s->trail_lim) );
//    start = (s->root_level >= veci_size(&s->trail_lim))? s->qtail-1 : (veci_begin(&s->trail_lim))[s->root_level];
    for (i = s->qtail-1; i >= (veci_begin(&s->trail_lim))[0]; i--){
        x = lit_var(s->trail[i]);
        if (var_tag(s,x)){
            satset* c = clause_read(s, var_reason(s,x));
            if (c){
                proof_chain_resolve( s, c, x );
                satset_foreach_var( c, x, j, 1 ){
                    if ( var_level(s,x) )
                        var_set_tag(s, x, 1);
                    else
                        proof_chain_resolve( s, NULL, x );
                } 
            }else {
                assert( var_level(s,x) );
                veci_push(&s->conf_final,lit_neg(s->trail[i]));
            }
        }
    }
    solver2_clear_tags(s,0);
    return proof_chain_stop( s );
}

static int solver2_lit_removable_rec(sat_solver2* s, int v)
{
    // tag[0]: True if original conflict clause literal.
    // tag[1]: Processed by this procedure
    // tag[2]: 0=non-removable, 1=removable

    satset* c;
    int i, x;

    // skip visited
    if (var_tag(s,v) & 2)
        return (var_tag(s,v) & 4) > 0;

    // skip decisions on a wrong level
    c = clause_read(s, var_reason(s,v));
    if ( c == NULL ){
        var_add_tag(s,v,2);
        return 0;
    }

    satset_foreach_var( c, x, i, 1 ){
        if (var_tag(s,x) & 1)
            solver2_lit_removable_rec(s, x);
        else{
            if (var_level(s,x) == 0 || var_tag(s,x) == 6) continue;     // -- 'x' checked before, found to be removable (or belongs to the toplevel)
            if (var_tag(s,x) == 2 || !var_lev_mark(s,x) || !solver2_lit_removable_rec(s, x))
            {  // -- 'x' checked before, found NOT to be removable, or it belongs to a wrong level, or cannot be removed
                var_add_tag(s,v,2); 
                return 0; 
            }
        }
    }
    if ( s->fProofLogging && (var_tag(s,v) & 1) )
        veci_push(&s->min_lit_order, v );
    var_add_tag(s,v,6);
    return 1;
}

static int solver2_lit_removable(sat_solver2* s, int x)
{
    satset* c;
    int i, top;
    if ( !var_reason(s,x) )
        return 0;
    if ( var_tag(s,x) & 2 )
    {
        assert( var_tag(s,x) & 1 );
        return 1;
    }
    top = veci_size(&s->tagged);
    veci_resize(&s->stack,0);
    veci_push(&s->stack, x << 1);
    while (veci_size(&s->stack))
    {
        x = veci_pop(&s->stack);
        if ( s->fProofLogging ){
            if ( x & 1 ){
                if ( var_tag(s,x >> 1) & 1 )
                    veci_push(&s->min_lit_order, x >> 1 );
                continue;
            }
            veci_push(&s->stack, x ^ 1 );
        }
        x >>= 1;
        c = clause_read(s, var_reason(s,x));
        satset_foreach_var( c, x, i, 1 ){
            if (var_tag(s,x) || !var_level(s,x))
                continue;
            if (!var_reason(s,x) || !var_lev_mark(s,x)){
                solver2_clear_tags(s, top);
                return 0;
            }
            veci_push(&s->stack, x << 1);
            var_set_tag(s, x, 2);
        }
    }
    return 1;
}

static void solver2_logging_order(sat_solver2* s, int x)
{
    satset* c;
    int i;
    if ( (var_tag(s,x) & 4) )
        return;
    var_add_tag(s, x, 4);
    veci_resize(&s->stack,0);
    veci_push(&s->stack,x << 1);
    while (veci_size(&s->stack))
    {
        x = veci_pop(&s->stack);
        if ( x & 1 ){
            veci_push(&s->min_step_order, x >> 1 );
            continue;
        }
        veci_push(&s->stack, x ^ 1 );
        x >>= 1;
        c = clause_read(s, var_reason(s,x));
//        if ( !c )
//            printf( "solver2_logging_order(): Error in conflict analysis!!!\n" );
        satset_foreach_var( c, x, i, 1 ){
            if ( !var_level(s,x) || (var_tag(s,x) & 1) )
                continue;
            veci_push(&s->stack, x << 1);
            var_add_tag(s, x, 4);
        }
    }
}

static void solver2_logging_order_rec(sat_solver2* s, int x)
{
    satset* c;
    int i, y;
    if ( (var_tag(s,x) & 8) )
        return;
    c = clause_read(s, var_reason(s,x));
    satset_foreach_var( c, y, i, 1 )
        if ( var_level(s,y) && (var_tag(s,y) & 1) == 0 )
            solver2_logging_order_rec(s, y);
    var_add_tag(s, x, 8);
    veci_push(&s->min_step_order, x);
}

static int solver2_analyze(sat_solver2* s, satset* c, veci* learnt)
{
    int cnt      = 0;
    lit p        = 0;
    int x, ind   = s->qtail-1;
    int proof_id = 0;
    lit* lits,* vars, i, j, k;
    assert( veci_size(&s->tagged) == 0 );
    // tag[0] - visited by conflict analysis (afterwards: literals of the learned clause)
    // tag[1] - visited by solver2_lit_removable() with success
    // tag[2] - visited by solver2_logging_order()

    proof_chain_start( s, c );
    veci_push(learnt,lit_Undef);
    while ( 1 ){
        assert(c != 0);
        if (c->learnt)
            act_clause_bump(s,c);
        satset_foreach_var( c, x, j, (int)(p > 0) ){
            assert(x >= 0 && x < s->size);
            if ( var_tag(s, x) )
                continue;
            if ( var_level(s,x) == 0 )
            {
                proof_chain_resolve( s, NULL, x );
                continue;
            }
            var_set_tag(s, x, 1);
            act_var_bump(s,x);
            if (var_level(s,x) == solver2_dlevel(s))
                cnt++;
            else
                veci_push(learnt,c->pEnts[j]);
        }

        while (!var_tag(s, lit_var(s->trail[ind--])));

        p = s->trail[ind+1];
        c = clause_read(s, lit_reason(s,p));
        cnt--;
        if ( cnt == 0 )
            break;
        proof_chain_resolve( s, c, lit_var(p) );
    }
    *veci_begin(learnt) = lit_neg(p);

    // mark levels
    assert( veci_size(&s->mark_levels) == 0 );
    lits = veci_begin(learnt);
    for (i = 1; i < veci_size(learnt); i++)
        var_lev_set_mark(s, lit_var(lits[i]));

    // simplify (full)
    veci_resize(&s->min_lit_order, 0);
    for (i = j = 1; i < veci_size(learnt); i++){
//        if (!solver2_lit_removable( s,lit_var(lits[i])))
        if (!solver2_lit_removable_rec(s,lit_var(lits[i]))) // changed to vars!!!
            lits[j++] = lits[i];
    } 

    // record the proof
    if ( s->fProofLogging )
    {
        // collect additional clauses to resolve
        veci_resize(&s->min_step_order, 0);
        vars = veci_begin(&s->min_lit_order);
        for (i = 0; i < veci_size(&s->min_lit_order); i++)
//            solver2_logging_order(s, vars[i]);
            solver2_logging_order_rec(s, vars[i]);

        // add them in the reverse order
        vars = veci_begin(&s->min_step_order);
        for (i = veci_size(&s->min_step_order); i > 0; ) { i--;
            c = clause_read(s, var_reason(s,vars[i]));
            proof_chain_resolve( s, c, vars[i] );
            satset_foreach_var(c, x, k, 1)
                if ( var_level(s,x) == 0 )
                    proof_chain_resolve( s, NULL, x );
        }
        proof_id = proof_chain_stop( s );
    }

    // unmark levels
    solver2_clear_marks( s );

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
    return proof_id;
}

satset* solver2_propagate(sat_solver2* s)
{
    satset* c, * confl  = NULL;
    veci* ws;
    lit* lits, false_lit, p, * stop, * k;
    cla* begin,* end, *i, *j;
    int Lit;

    while (confl == 0 && s->qtail - s->qhead > 0){

        p  = s->trail[s->qhead++];
        ws = solver2_wlist(s,p);
        begin = (cla*)veci_begin(ws);
        end   = begin + veci_size(ws);

        s->stats.propagations++;
        for (i = j = begin; i < end; ){
            c = clause_read(s,*i);
            lits = c->pEnts;

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
                stop = lits + c->nEnts;
                for (k = lits + 2; k < stop; k++){
                    if (var_value(s, lit_var(*k)) != !lit_sign(*k)){
                        lits[1] = *k;
                        *k = false_lit;
                        veci_push(solver2_wlist(s,lit_neg(lits[1])),*i);
                        goto WatchFound; }
                }

                // Did not find watch -- clause is unit under assignment:
                Lit = lits[0];
                if (s->fProofLogging && solver2_dlevel(s) == 0){
                    int k, x, proof_id, Cid, Var = lit_var(Lit);
                    int fLitIsFalse = (var_value(s, Var) == !lit_sign(Lit)); 
                    // Log production of top-level unit clause:
                    proof_chain_start( s, c );
                    satset_foreach_var( c, x, k, 1 ){
                        assert( var_level(s, x) == 0 );
                        proof_chain_resolve( s, NULL, x );
                    }
                    proof_id = proof_chain_stop( s );
                    // get a new clause
                    Cid = clause_create_new( s, &Lit, &Lit + 1, 1, proof_id );
                    assert( (var_unit_clause(s, Var) == NULL) != fLitIsFalse ); 
                    // if variable already has unit clause, it must be with the other polarity 
                    // in this case, we should derive the empty clause here
                    if ( var_unit_clause(s, Var) == NULL )
                        var_set_unit_clause(s, Var, Cid);
                    else{
                        // Empty clause derived:
                        proof_chain_start( s, clause_read(s,Cid) );
                        proof_chain_resolve( s, NULL, Var );
                        proof_id = proof_chain_stop( s );
                        s->hProofLast = proof_id;
//                        clause_create_new( s, &Lit, &Lit, 1, proof_id );
                    }
                }

                *j++ = *i;
                // Clause is unit under assignment:
                if (!solver2_enqueue(s,Lit, *i)){
                    confl = clause_read(s,*i++);
                    // Copy the remaining watches:
                    while (i < end)
                        *j++ = *i++;
                }
            }
WatchFound: i++;
        }
        s->stats.inspects += j - (int*)veci_begin(ws);
        veci_resize(ws,j - (int*)veci_begin(ws));
    }

    return confl;
}

int sat_solver2_simplify(sat_solver2* s)
{
    assert(solver2_dlevel(s) == 0);
    return (solver2_propagate(s) == NULL);
}

/*
 
void solver2_reducedb(sat_solver2* s)
{
    satset* c;
    cla Cid;
    int clk = clock();

    // sort the clauses by activity
    int nLearnts = veci_size(&s->claActs) - 1;
    extern int * Abc_SortCost( int * pCosts, int nSize );
    int * pPerm, * pCosts = veci_begin(&s->claActs);
    pPerm = Abc_SortCost( pCosts, veci_size(&s->claActs) );
    assert( pCosts[pPerm[1]] <= pCosts[pPerm[veci_size(&s->claActs)-1]] );

    // mark clauses to be removed
    {
        double   extra_limD = (double)s->cla_inc / nLearnts; // Remove any clause below this activity
        unsigned extra_lim  = (extra_limD < 1.0) ? 1 : (int)extra_limD;
        unsigned * pActs = (unsigned *)veci_begin(&s->claActs);
        int k = 1, Counter = 0;
        sat_solver_foreach_learnt( s, c, Cid )
        {
            assert( c->Id == k );
            c->mark = 0;
            if ( c->nEnts > 2 && lit_reason(s,c->pEnts[0]) != Cid && (k < nLearnts/2 || pActs[k] < extra_lim) )
            {
                c->mark = 1;
                Counter++;
            }
            k++;
        }
printf( "ReduceDB removed %10d clauses (out of %10d)... Cutoff = %8d  ", Counter, nLearnts, extra_lim );
Abc_PrintTime( 1, "Time", clock() - clk );
    }
    ABC_FREE( pPerm );
}
*/


static lbool solver2_search(sat_solver2* s, ABC_INT64_T nof_conflicts)
{
    double  random_var_freq = s->fNotUseRandom ? 0.0 : 0.02;

    ABC_INT64_T  conflictC       = 0;
    veci    learnt_clause;
    int     proof_id;

    assert(s->root_level == solver2_dlevel(s));

    s->stats.starts++;
//    s->var_decay = (float)(1 / 0.95   );
//    s->cla_decay = (float)(1 / 0.999);
    veci_new(&learnt_clause);

    for (;;){
        satset* confl = solver2_propagate(s);
        if (confl != 0){
            // CONFLICT
            int blevel;

#ifdef VERBOSEDEBUG
            printf(L_IND"**CONFLICT**\n", L_ind);
#endif
            s->stats.conflicts++; conflictC++;
            if (solver2_dlevel(s) <= s->root_level){
                proof_id = solver2_analyze_final(s, confl, 0);
                assert( proof_id > 0 );
//                solver2_record(s,&s->conf_final, proof_id);
                s->hProofLast = proof_id;
                veci_delete(&learnt_clause);
                return l_False;
            }

            veci_resize(&learnt_clause,0);
            proof_id = solver2_analyze(s, confl, &learnt_clause);
            blevel = veci_size(&learnt_clause) > 1 ? var_level(s, lit_var(veci_begin(&learnt_clause)[1])) : s->root_level;
            blevel = s->root_level > blevel ? s->root_level : blevel;
            solver2_canceluntil(s,blevel);
            solver2_record(s,&learnt_clause, proof_id);
            // if (learnt_clause.size() == 1) level[var(learnt_clause[0])] = 0;    
            // (this is ugly (but needed for 'analyzeFinal()') -- in future versions, we will backtrack past the 'root_level' and redo the assumptions)
            if ( learnt_clause.size == 1 ) 
                var_set_level( s, lit_var(learnt_clause.ptr[0]), 0 );
            act_var_decay(s);
            act_clause_decay(s);

        }else{
            // NO CONFLICT
            int next;

            if (nof_conflicts >= 0 && conflictC >= nof_conflicts){
                // Reached bound on number of conflicts:
                s->progress_estimate = solver2_progress(s);
                solver2_canceluntil(s,s->root_level);
                veci_delete(&learnt_clause);
                return l_Undef; }

            if ( (s->nConfLimit && s->stats.conflicts > s->nConfLimit) ||
//                 (s->nInsLimit  && s->stats.inspects  > s->nInsLimit) )
                 (s->nInsLimit  && s->stats.propagations > s->nInsLimit) )
            {
                // Reached bound on number of conflicts:
                s->progress_estimate = solver2_progress(s);
                solver2_canceluntil(s,s->root_level);
                veci_delete(&learnt_clause);
                return l_Undef; 
            }

//            if (solver2_dlevel(s) == 0 && !s->fSkipSimplify)
                // Simplify the set of problem clauses:
//                sat_solver2_simplify(s);

            // New variable decision:
            s->stats.decisions++;
            next = order_select(s,(float)random_var_freq);

            if (next == var_Undef){
                // Model found:
                int i;
                for (i = 0; i < s->size; i++) 
                    s->model[i] = (var_value(s,i)==var1 ? l_True : l_False);
                solver2_canceluntil(s,s->root_level);
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
                solver2_assume(s,toLit(next));
            else
                solver2_assume(s,lit_neg(toLit(next)));
        }
    }

    return l_Undef; // cannot happen
}

//=================================================================================================
// External solver functions:

sat_solver2* sat_solver2_new(void)
{
    sat_solver2* s = (sat_solver2 *)ABC_CALLOC( char, sizeof(sat_solver2) );

    // initialize vectors
    veci_new(&s->order);
    veci_new(&s->trail_lim);
    veci_new(&s->tagged);
    veci_new(&s->stack);
    veci_new(&s->temp_clause);
    veci_new(&s->conf_final);
    veci_new(&s->mark_levels);
    veci_new(&s->min_lit_order); 
    veci_new(&s->min_step_order);
    veci_new(&s->learnt_live);
    veci_new(&s->claActs);    veci_push(&s->claActs,   -1);
    veci_new(&s->claProofs);  veci_push(&s->claProofs, -1);

#ifdef USE_FLOAT_ACTIVITY2
    s->var_inc        = 1;
    s->cla_inc        = 1;
    s->var_decay      = (float)(1 / 0.95  );
    s->cla_decay      = (float)(1 / 0.999 );
//    s->cla_decay      = 1;
//    s->var_decay      = 1;
#else
    s->var_inc        = (1 <<  5);
    s->cla_inc        = (1 << 11);
#endif
    s->random_seed    = 91648253;

#ifdef SAT_USE_PROOF_LOGGING
    s->fProofLogging  =  1;
#else
    s->fProofLogging  =  0;
#endif
    s->fSkipSimplify  =  1;
    s->fNotUseRandom  =  0;

    // prealloc clause
    assert( !s->clauses.ptr );
    s->clauses.cap = (1 << 20);
    s->clauses.ptr = ABC_ALLOC( int, s->clauses.cap );
    veci_push(&s->clauses, -1);
    // prealloc learnt
    assert( !s->learnts.ptr );
    s->learnts.cap = (1 << 20);
    s->learnts.ptr = ABC_ALLOC( int, s->learnts.cap );
    veci_push(&s->learnts, -1);
    // prealloc proofs
    if ( s->fProofLogging )
    {
        assert( !s->proofs.ptr );
        s->proofs.cap = (1 << 20);
        s->proofs.ptr = ABC_ALLOC( int, s->proofs.cap );
        veci_push(&s->proofs, -1);
    }
    // initialize clause pointers
    s->hLearntLast    = -1; // the last learnt clause 
    s->hProofLast     = -1; // the last proof ID
    s->hClausePivot   =  1; // the pivot among clauses
    s->hLearntPivot   =  1; // the pivot moang learned clauses
    s->iVarPivot      =  0; // the pivot among the variables
    s->iSimpPivot     =  0; // marker of unit-clauses
    return s;
}


void sat_solver2_setnvars(sat_solver2* s,int n)
{
    int var;

    if (s->cap < n){
        int old_cap = s->cap;
        while (s->cap < n) s->cap = s->cap*2+1;

        s->wlists    = ABC_REALLOC(veci,     s->wlists,   s->cap*2);
        s->vi        = ABC_REALLOC(varinfo2, s->vi,       s->cap);
        s->levels    = ABC_REALLOC(int,      s->levels,   s->cap);
        s->assigns   = ABC_REALLOC(char,     s->assigns,  s->cap);
        s->trail     = ABC_REALLOC(lit,      s->trail,    s->cap);
        s->orderpos  = ABC_REALLOC(int,      s->orderpos, s->cap);
        s->reasons   = ABC_REALLOC(cla,      s->reasons,  s->cap);
        if ( s->fProofLogging )
        s->units     = ABC_REALLOC(cla,      s->units,    s->cap);
#ifdef USE_FLOAT_ACTIVITY2
        s->activity  = ABC_REALLOC(double,   s->activity, s->cap);
#else
        s->activity  = ABC_REALLOC(unsigned, s->activity, s->cap);
#endif
        s->model     = ABC_REALLOC(int,      s->model,    s->cap);
        memset( s->wlists + 2*old_cap, 0, 2*(s->cap-old_cap)*sizeof(vecp) );
    }

    for (var = s->size; var < n; var++){
        assert(!s->wlists[2*var].size);
        assert(!s->wlists[2*var+1].size);
        if ( s->wlists[2*var].ptr == NULL )
            veci_new(&s->wlists[2*var]);
        if ( s->wlists[2*var+1].ptr == NULL )
            veci_new(&s->wlists[2*var+1]);
        *((int*)s->vi + var) = 0; //s->vi[var].val = varX;
        s->levels  [var] = 0;
        s->assigns [var] = varX;
        s->orderpos[var] = veci_size(&s->order);
        s->reasons [var] = 0;        
        if ( s->fProofLogging )
        s->units   [var] = 0;        
#ifdef USE_FLOAT_ACTIVITY2
        s->activity[var] = 0;
#else
        s->activity[var] = (1<<10);
#endif
        s->model   [var] = 0; 
        // does not hold because variables enqueued at top level will not be reinserted in the heap
        // assert(veci_size(&s->order) == var); 
        veci_push(&s->order,var);
        order_update(s, var);
    }
    s->size = n > s->size ? n : s->size;
}

void sat_solver2_delete(sat_solver2* s)
{
//    veci * pCore;

    // report statistics
    printf( "Used %6.2f Mb for proof-logging.   Unit clauses = %d.\n", 2.0 * veci_size(&s->proofs) / (1<<20), s->nUnits );
/*
    pCore = Sat_ProofCore( s );
    printf( "UNSAT core contains %d clauses (%6.2f %%).\n", veci_size(pCore), 100.0*veci_size(pCore)/veci_size(&s->clauses) );
    veci_delete( pCore );
    ABC_FREE( pCore ); 

    if ( s->fProofLogging )
        Sat_ProofCheck( s );
*/
    // delete vectors
    veci_delete(&s->order);
    veci_delete(&s->trail_lim);
    veci_delete(&s->tagged);
    veci_delete(&s->stack);
    veci_delete(&s->temp_clause);
    veci_delete(&s->conf_final);
    veci_delete(&s->mark_levels);
    veci_delete(&s->min_lit_order);
    veci_delete(&s->min_step_order);
    veci_delete(&s->learnt_live);
    veci_delete(&s->proofs);
    veci_delete(&s->claActs);
    veci_delete(&s->claProofs);
    veci_delete(&s->clauses);
    veci_delete(&s->learnts);

    // delete arrays
    if (s->vi != 0){
        int i;
        if ( s->wlists )
            for (i = 0; i < s->cap*2; i++)
                veci_delete(&s->wlists[i]);
        ABC_FREE(s->wlists   );
        ABC_FREE(s->vi       );
        ABC_FREE(s->levels   );
        ABC_FREE(s->assigns  );
        ABC_FREE(s->trail    );
        ABC_FREE(s->orderpos );
        ABC_FREE(s->reasons  );
        ABC_FREE(s->units    );
        ABC_FREE(s->activity );
        ABC_FREE(s->model    );
    }
    ABC_FREE(s);
}


int sat_solver2_addclause(sat_solver2* s, lit* begin, lit* end)
{
    cla Cid;
    lit *i,*j,*iFree = NULL;
    int maxvar, count, temp;
    assert( solver2_dlevel(s) == 0 );
    assert( begin < end );

    // copy clause into storage
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
    sat_solver2_setnvars(s,maxvar+1);

    // coount the number of 0-literals
    count = 0;
    for ( i = begin; i < end; i++ )
    {
        // make sure all literals are unique
        assert( i == begin || lit_var(*(i-1)) != lit_var(*i) );
        // consider the value of this literal
        if ( var_value(s, lit_var(*i)) == lit_sign(*i) ) // this clause is always true
            return clause_create_new( s, begin, end, 0, 0 ); // add it anyway, to preserve proper clause count       
        if ( var_value(s, lit_var(*i)) == varX ) // unassigned literal
            iFree = i;
        else
            count++; // literal is 0
    }
    assert( count < end-begin ); // the clause cannot be UNSAT

    // swap variables to make sure the clause is watched using unassigned variable
    temp   = *iFree;
    *iFree = *begin;
    *begin = temp;

    // create a new clause
    Cid = clause_create_new( s, begin, end, 0, 0 );

    // handle unit clause
    if ( count+1 == end-begin )
    {
        if ( s->fProofLogging )
        {
            if ( count == 0 ) // original learned clause
            {
                var_set_unit_clause( s, lit_var(begin[0]), Cid );
                if ( !solver2_enqueue(s,begin[0],0) )
                    assert( 0 );
            }
            else
            {
                // Log production of top-level unit clause:
                int x, k, proof_id, CidNew;
                satset* c = clause_read(s, Cid);
                proof_chain_start( s, c );
                satset_foreach_var( c, x, k, 1 )
                    proof_chain_resolve( s, NULL, x );
                proof_id = proof_chain_stop( s );
                // generate a new clause
                CidNew = clause_create_new( s, begin, begin+1, 1, proof_id );
                var_set_unit_clause( s, lit_var(begin[0]), CidNew );
                if ( !solver2_enqueue(s,begin[0],Cid) )
                    assert( 0 );
            }
        }
    }
    return Cid;
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


// updates clauses, watches, units, and proof
void solver2_reducedb(sat_solver2* s)
{
    satset * c;
    cla h,* pArray,* pArray2;
    int Counter = 0, CounterStart = s->stats.learnts * 3 / 4; // 2/3;
    int i, j, k, hTemp, hHandle, clk = clock();
    static int TimeTotal = 0;

    // remove 2/3 of learned clauses while skipping small clauses
    veci_resize( &s->learnt_live, 0 );
    sat_solver_foreach_learnt( s, c, h )
        if ( Counter++ > CounterStart || c->nEnts < 3 )
            veci_push( &s->learnt_live, h );
        else
            c->mark = 1;
    // report the results
    printf( "reduceDB: Keeping %7d out of %7d clauses (%5.2f %%)  ", 
        veci_size(&s->learnt_live), s->stats.learnts, 100.0 * veci_size(&s->learnt_live) / s->stats.learnts );

    // remap clause proofs and clauses
    hHandle = 1;
    pArray  = s->fProofLogging ? veci_begin(&s->claProofs) : NULL;
    pArray2 = veci_begin(&s->claActs);
    satset_foreach_entry_vec( &s->learnt_live, &s->learnts, c, i )
    {
        if ( pArray )
        pArray[i+1]  = pArray[c->Id];
        pArray2[i+1] = pArray2[c->Id];
        c->Id = hHandle; hHandle += satset_size(c->nEnts);
    }
    if ( s->fProofLogging )
    veci_resize(&s->claProofs,veci_size(&s->learnt_live)+1);
    veci_resize(&s->claActs,veci_size(&s->learnt_live)+1);

    // compact watches 
    for ( i = 0; i < s->size*2; i++ )
    {
        pArray = veci_begin(&s->wlists[i]);
        for ( j = k = 0; k < veci_size(&s->wlists[i]); k++ )
            if ( !(pArray[k] & 1) ) // problem clause
                pArray[j++] = pArray[k];
            else if ( !(c = clause_read(s, pArray[k]))->mark ) // useful learned clause
                pArray[j++] = (c->Id << 1) | 1;
        veci_resize(&s->wlists[i],j);
    }
    // compact units
    if ( s->fProofLogging )
    for ( i = 0; i < s->size; i++ )
        if ( s->units[i] && (s->units[i] & 1) )
            s->units[i] = (clause_read(s, s->units[i])->Id << 1) | 1;
    // compact clauses
    satset_foreach_entry_vec( &s->learnt_live, &s->learnts, c, i )
    {
        hTemp = c->Id; c->Id = i + 1;
        memmove( veci_begin(&s->learnts) + hTemp, c, sizeof(int)*satset_size(c->nEnts) );
    }
    assert( hHandle == hTemp + satset_size(c->nEnts) );
    veci_resize(&s->learnts,hHandle);
    s->stats.learnts = veci_size(&s->learnt_live);

    // compact proof (compacts 'proofs' and update 'claProofs')
    if ( s->fProofLogging )
    Sat_ProofReduce( s );

    TimeTotal += clock() - clk;
    Abc_PrintTime( 1, "Time", TimeTotal );
}

// reverses to the previously bookmarked point
void sat_solver2_rollback( sat_solver2* s )
{
    int i, k, j;
    assert( s->qhead == s->qtail );
    assert( s->hClausePivot >= 1 && s->hClausePivot <= veci_size(&s->clauses) );
    assert( s->hLearntPivot >= 1 && s->hLearntPivot <= veci_size(&s->learnts) );
    assert( s->iVarPivot >= 0 && s->iVarPivot <= s->size );
    veci_resize(&s->order, 0);
    if ( s->hClausePivot > 1 || s->hLearntPivot > 1 )
    { 
        // update order 
        for ( i = 0; i < s->iVarPivot; i++ )
        {
            if ( var_value(s, i) != varX )
                continue;
            s->orderpos[i] = veci_size(&s->order);
            veci_push(&s->order,i);
            order_update(s, i);
        }
        // compact watches
        for ( i = 0; i < s->size*2; i++ )
        {
            cla* pArray = veci_begin(&s->wlists[i]);
            for ( j = k = 0; k < veci_size(&s->wlists[i]); k++ )
                if ( clause_is_used(s, pArray[k]) )
                    pArray[j++] = pArray[k];
            veci_resize(&s->wlists[i],j);
        }
    }
    // reset implication queue
    assert( (&s->trail_lim)->ptr[0] >= s->iSimpPivot );
    (&s->trail_lim)->ptr[0] = s->iSimpPivot;
    solver2_canceluntil( s, 0 );
    // reset problem clauses
    if ( s->hClausePivot < veci_size(&s->clauses) )
    {
        satset* first = satset_read(&s->clauses, s->hClausePivot);
        s->stats.clauses = first->Id-1;
        veci_resize(&s->clauses, s->hClausePivot);
    }
    // resetn learned clauses
    if ( s->hLearntPivot < veci_size(&s->learnts) )
    { 
        satset* first = satset_read(&s->learnts, s->hLearntPivot);
        veci_resize(&s->claActs,   first->Id);
        if ( s->fProofLogging ) {
            veci_resize(&s->claProofs, first->Id);
            Sat_ProofReduce( s );
        }
        s->stats.learnts = first->Id-1;
        veci_resize(&s->learnts, s->hLearntPivot);
    }
    // reset watcher lists
    for ( i = 2*s->iVarPivot; i < 2*s->size; i++ )
        s->wlists[i].size = 0;
    for ( i = s->iVarPivot; i < s->size; i++ )
    {
        *((int*)s->vi + i) = 0;
        s->levels  [i] = 0;
        s->assigns [i] = varX;
        s->reasons [i] = 0;        
        s->units   [i] = 0;        
#ifdef USE_FLOAT_ACTIVITY2
        s->activity[i] = 0;
#else
        s->activity[i] = (1<<10);
#endif
        s->model   [i] = 0; 
    }
    s->size = s->iVarPivot;
    // initialize other vars
    if ( s->size == 0 )
    {
    //    s->size                   = 0;
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
        // initialize clause pointers
        s->hLearntLast    = -1; // the last learnt clause 
        s->hProofLast     = -1; // the last proof ID
        s->hClausePivot   =  1; // the pivot among clauses
        s->hLearntPivot   =  1; // the pivot moang learned clauses
        s->iVarPivot      =  0; // the pivot among the variables
        s->iSimpPivot     =  0; // marker of unit-clauses
    }
}

// find the clause in the watcher lists
int sat_solver2_find_clause( sat_solver2* s, int Hand, int fVerbose )
{
    int i, k, Found = 0;
    if ( Hand >= s->clauses.size )
        return 1;
    for ( i = 0; i < s->size*2; i++ )
    {
        cla* pArray = veci_begin(&s->wlists[i]);
        for ( k = 0; k < veci_size(&s->wlists[i]); k++ )
            if ( (pArray[k] >> 1) == Hand )
            {
                if ( fVerbose )
                printf( "Clause found in list %d.\n", k );
                Found = 1;
                break;
            }
    }
    if ( Found == 0 )
    {
        if ( fVerbose )
        printf( "Clause with hand %d is not found.\n", Hand );
    }
    return Found;
}

// verify that all clauses are satisfied
void sat_solver2_verify( sat_solver2* s )
{
    satset * c;
    int i, k, v, Counter = 0;
    satset_foreach_entry( &s->clauses, c, i, 1 )
    {
        for ( k = 0; k < (int)c->nEnts; k++ )
        {
            v = lit_var(c->pEnts[k]);
            if ( sat_solver2_var_value(s, v) ^ lit_sign(c->pEnts[k]) )
                break;
        }
        if ( k == (int)c->nEnts )
        {
            printf( "Clause %d is not satisfied.   ", c->Id );
            satset_print( c );
            sat_solver2_find_clause( s, satset_handle(&s->clauses, c), 1 );
            Counter++;
        }
    }
    if ( Counter != 0 )
        printf( "Verification failed!\n" );
//    else
//        printf( "Verification passed.\n" );
}


int sat_solver2_solve(sat_solver2* s, lit* begin, lit* end, ABC_INT64_T nConfLimit, ABC_INT64_T nInsLimit, ABC_INT64_T nConfLimitGlobal, ABC_INT64_T nInsLimitGlobal)
{
    int restart_iter = 0;
    ABC_INT64_T  nof_conflicts;
    ABC_INT64_T  nof_learnts   = sat_solver2_nclauses(s) / 3;
    lbool status = l_Undef;
    int proof_id;
    lit * i;

    s->hLearntLast = -1;
    s->hProofLast = -1;

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

/*
    // Perform assumptions:
    root_level = assumps.size();
    for (int i = 0; i < assumps.size(); i++){
        Lit p = assumps[i];
        assert(var(p) < nVars());
        if (!solver2_assume(p)){
            GClause r = reason[var(p)];
            if (r != GClause_NULL){
                satset* confl;
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
        satset* confl = propagate();
        if (confl != NULL){
            analyzeFinal(confl), assert(conflict.size() > 0);
            cancelUntil(0);
            return false; }
    }
    assert(root_level == decisionLevel());
*/

    // Perform assumptions:
    s->root_level = end - begin;
    for ( i = begin; i < end; i++ )
    {
        lit p = *i;
        assert(lit_var(p) < s->size);
        veci_push(&s->trail_lim,s->qtail);
        if (!solver2_enqueue(s,p,0))
        {
            satset* r = clause_read(s, lit_reason(s,p));
            if (r != NULL)
            {
                satset* confl = r;
                proof_id = solver2_analyze_final(s, confl, 1);
                veci_push(&s->conf_final, lit_neg(p));
            }
            else
            {
                assert( 0 );
                proof_id = -1; // the only case when ProofId is not assigned (conflicting assumptions)
                veci_resize(&s->conf_final,0);
                veci_push(&s->conf_final, lit_neg(p));
                // the two lines below are a bug fix by Siert Wieringa 
                if (var_level(s, lit_var(p)) > 0) 
                    veci_push(&s->conf_final, p);
            }
//            solver2_record(s, &s->conf_final, proof_id, 1);
            s->hProofLast = proof_id;
            solver2_canceluntil(s, 0);
            return l_False; 
        }
        else
        {
            satset* confl = solver2_propagate(s);
            if (confl != NULL){
                proof_id = solver2_analyze_final(s, confl, 0);
                assert(s->conf_final.size > 0);
//                solver2_record(s,&s->conf_final, proof_id, 1);
                s->hProofLast = proof_id;
                solver2_canceluntil(s, 0);
                return l_False; 
            }
        }
    }
    assert(s->root_level == solver2_dlevel(s));

    if (s->verbosity >= 1){
        printf("==================================[MINISAT]===================================\n");
        printf("| Conflicts |     ORIGINAL     |              LEARNT              | Progress |\n");
        printf("|           | Clauses Literals |   Limit Clauses Literals  Lit/Cl |          |\n");
        printf("==============================================================================\n");
    }

    while (status == l_Undef){
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
                (s->stats.learnts == 0)? 0.0 : (double)s->stats.learnts_literals / s->stats.learnts,
                s->progress_estimate*100);
            fflush(stdout);
        }
        if ( s->nRuntimeLimit && time(NULL) > s->nRuntimeLimit )
            break;
         // reduce the set of learnt clauses:
        if (nof_learnts > 0 && s->stats.learnts > nof_learnts)
        {
//            solver2_reducedb(s);
            nof_learnts = nof_learnts * 11 / 10;
        }
        // perform next run
        nof_conflicts = (ABC_INT64_T)( 100 * luby2(2, restart_iter++) );
        status = solver2_search(s, nof_conflicts);
        // quit the loop if reached an external limit
        if ( s->nConfLimit && s->stats.conflicts > s->nConfLimit )
            break;
        if ( s->nInsLimit  && s->stats.propagations > s->nInsLimit )
            break;
    }
    if (s->verbosity >= 1)
        printf("==============================================================================\n");

    solver2_canceluntil(s,0);
    assert( s->qhead == s->qtail );
//    if ( status == l_True )
//        sat_solver2_verify( s );
    return status;
}


ABC_NAMESPACE_IMPL_END

