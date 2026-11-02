/**CFile****************************************************************

  FileName    [decplaCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Cube-based decomposition of incompletely specified functions.]

  Synopsis    [Cover consistency, greedy support reduction, and compatibility.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 28, 2026.]

  Revision    [$Id: decplaCore.c,v 1.00 2026/09/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "decplaInt.h"
ABC_NAMESPACE_IMPL_START

static int Decpla_Disjoint( const word * a, const word * b, int n, int skip )
{
    int i;
    for ( i = 0; i < n; ++i ) {
        word t = a[i] | b[i];
        if ( skip >= 0 && i == skip / 32 ) t &= ~((word)3 << (2*(skip%32)));
        if ( t & (t >> 1) & ABC_CONST(0x5555555555555555) ) return 1;
    }
    return 0;
}
static int Decpla_CoversDisjoint( const Decpla_Cover_t * a, const Decpla_Cover_t * b, int skip )
{
    size_t i, j;
    for ( i = 0; i < a->nCubes; ++i ) for ( j = 0; j < b->nCubes; ++j )
        if ( !Decpla_Disjoint(a->pData+i*a->nWords, b->pData+j*b->nWords, a->nWords, skip) ) return 0;
    return 1;
}
int Decpla_Check( const Decpla_Man_t * p, FILE * err )
{
    int i;
    for ( i = 0; i < p->nOutputs; ++i )
        if ( !Decpla_CoversDisjoint(&p->pIsfs[i].On, &p->pIsfs[i].Off, -1) ) {
            fprintf(err, "decpla: output %d (%s): overlapping On/Off cubes\n", i, p->pOutputs ? p->pOutputs[i] : "positional"); return 0;
        }
    return 1;
}
static int Decpla_HasVar( const Decpla_Isf_t * p, int v )
{
    size_t k; int phase;
    for ( phase = 0; phase < 2; ++phase ) {
        const Decpla_Cover_t * c = phase ? &p->On : &p->Off;
        for ( k = 0; k < c->nCubes; ++k ) if ( Decpla_CubeLit(c->pData+k*c->nWords, v) ) return 1;
    }
    return 0;
}
int Decpla_SupportSize( const Decpla_Isf_t * p, int nInputs )
{
    int v, n = 0;
    for ( v = 0; v < nInputs; ++v ) n += Decpla_HasVar(p, v);
    return n;
}
// Remove duplicates and subsumed cubes. This is deliberately a simple
// quadratic baseline; large-cover indexing is a subsequent milestone.
static void Decpla_Compact( Decpla_Cover_t * c )
{
    size_t i, j; int w;
    for ( i = 0; i < c->nCubes; ) {
        int remove = 0;
        for ( j = 0; j < c->nCubes && !remove; ++j ) if ( i != j ) {
            const word * a = c->pData+j*c->nWords, * b = c->pData+i*c->nWords;
            for ( w = 0; w < c->nWords; ++w ) if ( a[w] & ~b[w] ) break;
            remove = w == c->nWords;
        }
        if ( remove ) { --c->nCubes; memmove(c->pData+i*c->nWords, c->pData+(i+1)*c->nWords, (c->nCubes-i)*c->nWords*sizeof(word)); }
        else ++i;
    }
}
/**Function*************************************************************

  Synopsis    [Removes redundant inputs in the given permutation order.]

  Description [A null order uses increasing input indices. Projection
               preserves disjoint On/Off covers at each deletion.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Decpla_MinimizeOrder( Decpla_Man_t * p, const int * order, FILE * err )
{
    int i, j, v, phase;
    if ( !Decpla_Check(p, err) ) return 0;
    for ( i = 0; i < p->nOutputs; ++i ) {
        Decpla_Isf_t * f = &p->pIsfs[i];
        for ( j = 0; j < p->nInputs; ++j ) {
            v = order ? order[j] : j;
            assert(v >= 0 && v < p->nInputs);
            if ( !Decpla_HasVar(f, v) || !Decpla_CoversDisjoint(&f->On, &f->Off, v) ) continue;
            // Existential projection only expands requirements. Disjointness
            // proves that every completion of the result satisfies the input.
            for ( phase = 0; phase < 2; ++phase ) {
                Decpla_Cover_t * c = phase ? &f->On : &f->Off; size_t k;
                for ( k = 0; k < c->nCubes; ++k ) Decpla_CubeSet(c->pData+k*c->nWords, v, 0);
            }
        }
        Decpla_Compact(&f->On); Decpla_Compact(&f->Off);
    }
    return Decpla_Check(p, err);
}
int Decpla_Minimize( Decpla_Man_t * p, FILE * err )
{
    return Decpla_MinimizeOrder(p,NULL,err);
}
static int * Decpla_Match( char ** a, int na, char ** b, int nb, int complete, FILE * err )
{
    int i, j, * map;
    if ( (!!a != !!b) || ((!a || complete) && na != nb) ) {
        fprintf(err, "decpla: incompatible interface labels/counts (label both sides or neither)\n"); return NULL;
    }
    map = (int *)malloc(na * sizeof(int)); if ( !map ) return NULL;
    for ( i = 0; i < na; ++i ) {
        map[i] = a ? -1 : i;
        if ( a ) for ( j = 0; j < nb; ++j ) if ( !strcmp(a[i], b[j]) ) { map[i] = j; break; }
        if ( complete && map[i] < 0 ) { fprintf(err, "decpla: unmatched output %s\n", a[i]); free(map); return NULL; }
    }
    return map;
}
static int Decpla_MappedDisjoint( const Decpla_Cover_t * a, const Decpla_Cover_t * b, const int * map, int ni )
{
    size_t i, j; int v;
    for ( i = 0; i < a->nCubes; ++i ) for ( j = 0; j < b->nCubes; ++j ) {
        const word * x = a->pData+i*a->nWords, * y = b->pData+j*b->nWords;
        for ( v = 0; v < ni; ++v ) if ( map[v] >= 0 && (Decpla_CubeLit(x,v) | Decpla_CubeLit(y,map[v])) == 3 ) break;
        if ( v == ni ) return 0;
    }
    return 1;
}
int Decpla_Compatible( const Decpla_Man_t * p, const Decpla_Man_t * q, FILE * err )
{
    int i, result = 1;
    int * inputs = Decpla_Match(p->pInputs,p->nInputs,q->pInputs,q->nInputs,0,err);
    int * outputs = Decpla_Match(p->pOutputs,p->nOutputs,q->pOutputs,q->nOutputs,1,err);
    if ( !inputs || !outputs ) { free(inputs); free(outputs); return -1; }
    for ( i = 0; i < p->nOutputs; ++i ) {
        const Decpla_Isf_t * a = &p->pIsfs[i], * b = &q->pIsfs[outputs[i]];
        if ( !Decpla_MappedDisjoint(&a->On,&b->Off,inputs,p->nInputs) || !Decpla_MappedDisjoint(&a->Off,&b->On,inputs,p->nInputs) ) {
            fprintf(err, "decpla: conflicting requirements at output %d (%s)\n", i, p->pOutputs ? p->pOutputs[i] : "positional"); result = 0; break;
        }
    }
    free(inputs); free(outputs); return result;
}
ABC_NAMESPACE_IMPL_END
