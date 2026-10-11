/**CFile****************************************************************

  FileName    [decplaVerify.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Cube-based decomposition of incompletely specified functions.]

  Synopsis    [Ternary and SAT proofs of cube requirements on a completed AIG.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 28, 2026.]

  Revision    [$Id: decplaVerify.c,v 1.00 2026/09/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "decplaInt.h"
#include "sat/bsat/satSolver.h"
ABC_NAMESPACE_IMPL_START
struct Decpla_Sat_t_ {
    Gia_Man_t * g;
    sat_solver * s;
    unsigned char * values;
    int capacity, encoded, coneRoot, split;
    Vec_Int_t * assumptions, * cone, * stack;
};
Decpla_Sat_t * Decpla_SatStart( Gia_Man_t * g )
{
    Decpla_Sat_t * p = (Decpla_Sat_t *)calloc(1,sizeof(*p));
    if ( !p ) return NULL;
    p->g = g; p->s = sat_solver_new(); p->assumptions = Vec_IntAlloc(16);
    p->cone = Vec_IntAlloc(32); p->stack = Vec_IntAlloc(32);
    p->coneRoot = p->split = -1;
    return p;
}
void Decpla_SatStop( Decpla_Sat_t * p )
{
    if ( !p ) return;
    sat_solver_delete(p->s); Vec_IntFree(p->assumptions);
    Vec_IntFree(p->cone); Vec_IntFree(p->stack); free(p->values); free(p);
}
static int Decpla_Value( Decpla_Sat_t * p, int lit )
{ int v = p->values[lit>>1]; return v == 2 ? 2 : v ^ (lit&1); }

/**Function*************************************************************

  Synopsis    [Collects the literal's inputs and ANDs in evaluation order.]

  Description [The GIA only grows while this manager is active. A cached
               cone therefore remains valid when unrelated nodes are added.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Decpla_ConePrepare( Decpla_Sat_t * p, int lit )
{
    int id;
    Gia_Obj_t * obj;
    if ( p->coneRoot == (lit>>1) ) return Abc_MaxInt(1,Vec_IntSize(p->cone));
    if ( Gia_ManObjNum(p->g) > p->capacity ) {
        unsigned char * temp = (unsigned char *)realloc(p->values,Gia_ManObjNum(p->g));
        if ( !temp ) return -1;
        p->values = temp; p->capacity = Gia_ManObjNum(p->g);
    }
    Vec_IntClear(p->cone); Vec_IntClear(p->stack);
    Gia_ManIncrementTravId(p->g); Vec_IntPush(p->stack,lit>>1);
    while ( Vec_IntSize(p->stack) ) {
        id = Vec_IntPop(p->stack);
        if ( id < 0 ) { Vec_IntPush(p->cone,~id); continue; }
        if ( !id || Gia_ObjIsTravIdCurrentId(p->g,id) ) continue;
        Gia_ObjSetTravIdCurrentId(p->g,id);
        obj = Gia_ManObj(p->g,id);
        if ( Gia_ObjIsCi(obj) ) Vec_IntPush(p->cone,id);
        else {
            assert(Gia_ObjIsAnd(obj));
            Vec_IntPush(p->stack,~id);
            Vec_IntPush(p->stack,Gia_ObjFaninId0(obj,id));
            Vec_IntPush(p->stack,Gia_ObjFaninId1(obj,id));
        }
    }
    p->coneRoot = lit>>1;
    return Abc_MaxInt(1,Vec_IntSize(p->cone));
}

/**Function*************************************************************

  Synopsis    [Returns an unspecified input from the last evaluated cone.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Decpla_CubeSplit( Decpla_Sat_t * p )
{
    return p->split;
}

int Decpla_CubeEval( Decpla_Sat_t * p, const word * cube, int lit )
{
    int i, id, a, b;
    Gia_Obj_t * obj;
    if ( Decpla_ConePrepare(p,lit) < 0 ) return -1;
    p->values[0] = 0;
    p->split = -1;
    Vec_IntForEachEntry(p->cone,id,i) {
        obj = Gia_ManObj(p->g,id);
        if ( Gia_ObjIsCi(obj) ) {
            unsigned v = Decpla_CubeLit(cube,Gia_ObjCioId(obj));
            p->values[id] = (unsigned char)(v ? v-1 : 2);
            if ( !v && p->split < 0 ) p->split = Gia_ObjCioId(obj);
        } else {
            a = Decpla_Value(p,Gia_ObjFaninLit0(obj,id));
            b = Decpla_Value(p,Gia_ObjFaninLit1(obj,id));
            p->values[id] = (unsigned char)(a == 0 || b == 0 ? 0 : a == 1 && b == 1 ? 1 : 2);
        }
    }
    return Decpla_Value(p,lit);
}
static int Decpla_Encode( Decpla_Sat_t * p )
{
    int i, a, b, c, lits[3];
    sat_solver_setnvars(p->s,Gia_ManObjNum(p->g));
    if ( !p->encoded ) {
        lits[0] = 1;
        if ( !sat_solver_addclause(p->s,lits,lits+1) ) return 0;
        p->encoded = 1;
    }
    for ( i = p->encoded; i < Gia_ManObjNum(p->g); ++i ) {
        Gia_Obj_t * obj = Gia_ManObj(p->g,i);
        if ( !Gia_ObjIsAnd(obj) ) continue;
        a = Gia_ObjFaninLit0(obj,i); b = Gia_ObjFaninLit1(obj,i); c = 2*i;
        lits[0] = c^1; lits[1] = a;
        if ( !sat_solver_addclause(p->s,lits,lits+2) ) return 0;
        lits[1] = b;
        if ( !sat_solver_addclause(p->s,lits,lits+2) ) return 0;
        lits[0] = c; lits[1] = a^1; lits[2] = b^1;
        if ( !sat_solver_addclause(p->s,lits,lits+3) ) return 0;
    }
    p->encoded = Gia_ManObjNum(p->g); return 1;
}
int Decpla_CubeProve( Decpla_Sat_t * p, const word * cube, int lit, int value, int limit )
{
    int i, result = Decpla_CubeEval(p,cube,lit);
    if ( result < 0 ) return -1;
    if ( result < 2 ) return result == value;
    if ( !Decpla_Encode(p) ) return -1;
    Vec_IntClear(p->assumptions);
    for ( i = 0; i < Gia_ManCiNum(p->g); ++i ) {
        unsigned v = Decpla_CubeLit(cube,i);
        if ( v ) Vec_IntPush(p->assumptions,Gia_Obj2Lit(p->g,Gia_ManCi(p->g,i)) ^ (v == 1));
    }
    Vec_IntPush(p->assumptions,lit ^ value); // Seek a violating assignment.
    result = sat_solver_solve(p->s,Vec_IntArray(p->assumptions),Vec_IntArray(p->assumptions)+Vec_IntSize(p->assumptions),limit,0,0,0);
    return result == l_False ? 1 : result == l_True ? 0 : -1;
}
int Decpla_Verify( const Decpla_Man_t * p, Gia_Man_t * g, int limit, FILE * err )
{
    Decpla_Sat_t * s; int i, phase, result = 1;
    if ( Gia_ManRegNum(g) || Gia_ManCiNum(g) != p->nInputs || Gia_ManCoNum(g) != p->nOutputs || limit < 1 ) {
        fprintf(err,"decpla: verification interface/options mismatch\n"); return -1;
    }
    // Only ordinary AND/inverter GIAs are supported by this CNF encoder.
    if ( Gia_ManHasMapping(g) || Gia_ManMuxNum(g) || Gia_ManXorNum(g) || Gia_ManBufNum(g) ) {
        fprintf(err,"decpla: verification requires an ordinary AND/inverter AIG\n"); return -1;
    }
    s = Decpla_SatStart(g); if ( !s ) return -1;
    for ( i = 0; i < p->nOutputs && result == 1; ++i ) for ( phase = 0; phase < 2 && result == 1; ++phase ) {
        const Decpla_Cover_t * c = phase ? &p->pIsfs[i].On : &p->pIsfs[i].Off;
        int lit = Gia_ObjFaninLit0p(g,Gia_ManCo(g,i)); size_t k;
        for ( k = 0; k < c->nCubes; ++k ) {
            result = Decpla_CubeProve(s,c->pData+k*c->nWords,lit,phase,limit);
            if ( result != 1 ) {
                fprintf(err,"decpla: verification %s at output %d, %s cube %lu\n", result == 0 ? "FAILED" : "INCONCLUSIVE",i,phase ? "On" : "Off",(unsigned long)k);
                break;
            }
        }
    }
    Decpla_SatStop(s); return result;
}
ABC_NAMESPACE_IMPL_END
