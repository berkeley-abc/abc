/**CFile****************************************************************

  FileName    [decplaSupp.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Cube-based decomposition of incompletely specified functions.]

  Synopsis    [Seeded weighted hitting-set support selection.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 28, 2026.]

  Revision    [$Id: decplaSupp.c,v 1.00 2026/09/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "decpla.h"
ABC_NAMESPACE_IMPL_START

// One bit at each even position denotes a separating variable.
static void Decpla_Conflict( word * dst, const word * a, const word * b, int nw )
{
    int w;
    for ( w = 0; w < nw; ++w ) {
        word t = a[w] | b[w];
        dst[w] = t & (t >> 1) & ABC_CONST(0x5555555555555555);
    }
}
static unsigned Decpla_BitCount( word x )
{
    unsigned n = 0;
    while ( x ) { x &= x-1; ++n; }
    return n;
}
static word Decpla_Random( word * state )
{
    word z = (*state += ABC_CONST(0x9e3779b97f4a7c15));
    z = (z ^ (z >> 30)) * ABC_CONST(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)) * ABC_CONST(0x94d049bb133111eb);
    return z ^ (z >> 31);
}
// Rejection sampling avoids modulo bias when resolving score ties.
static unsigned Decpla_Choose( word * state, unsigned n )
{
    word x, threshold = (-(word)n) % n;
    do x = Decpla_Random(state); while ( x < threshold );
    return (unsigned)(x % n);
}
static int Decpla_Select( Decpla_Isf_t * f, int ni, word * state, size_t budget, FILE * err )
{
    int nw = f->On.nWords, w, v, phase, pass;
    size_t i, j, index, pairs = 0;
    word * cache = NULL, * tmp = NULL, * keep = NULL, * scores = NULL;
    int ok = 0;
    // Avoid multiplication overflow and never allocate an unbounded pair matrix.
    if ( f->Off.nCubes && f->On.nCubes <= budget / sizeof(word) / nw / f->Off.nCubes ) {
        pairs = f->On.nCubes * f->Off.nCubes;
        if ( pairs ) cache = (word *)malloc(pairs * nw * sizeof(word));
    }
    tmp = (word *)malloc(nw * sizeof(word));
    keep = (word *)calloc(nw, sizeof(word));
    scores = (word *)calloc(ni, sizeof(word));
    if ( !tmp || !keep || !scores ) { fprintf(err,"decpla: support-selection allocation failed\n"); goto done; }
    if ( cache ) {
        index = 0;
        for ( i = 0; i < f->On.nCubes; ++i ) for ( j = 0; j < f->Off.nCubes; ++j )
            Decpla_Conflict(cache + index++ * nw, f->On.pData+i*nw, f->Off.pData+j*nw, nw);
    }
    // First pass selects all mandatory singleton separators. Later passes
    // score only uncovered pairs. Integer 2^20/cardinality weights make
    // tie behavior independent of floating-point implementation details.
    for ( pass = 0; ; ++pass ) {
        int uncovered = 0, best = -1;
        unsigned ties = 0;
        word bestScore = 0;
        memset(scores,0,ni*sizeof(word)); index = 0;
        for ( i = 0; i < f->On.nCubes; ++i ) for ( j = 0; j < f->Off.nCubes; ++j, ++index ) {
            const word * c;
            unsigned count = 0;
            int hit = 0;
            if ( cache ) c = cache + index*nw;
            else { Decpla_Conflict(tmp,f->On.pData+i*nw,f->Off.pData+j*nw,nw); c = tmp; }
            for ( w = 0; w < nw; ++w ) { hit |= (c[w] & keep[w]) != 0; count += Decpla_BitCount(c[w]); }
            if ( hit ) continue;
            if ( !count ) { fprintf(err,"decpla: inconsistent support constraints\n"); goto done; }
            uncovered = 1;
            if ( pass == 0 && count != 1 ) continue;
            for ( w = 0; w < nw; ++w ) {
                word bits = c[w];
                while ( bits ) {
                    word bit = bits & (~bits+1), scan = bit;
                    unsigned pos = 0;
                    while ( (scan >>= 1) != 0 ) ++pos;
                    v = 32*w + (int)(pos/2);
                    if ( pass == 0 ) keep[w] |= bit;
                    else {
                        word weight = 1048576 / count;
                        if ( scores[v] > ~(word)0 - weight ) { fprintf(err,"decpla: support score overflow\n"); goto done; }
                        scores[v] += weight;
                    }
                    bits &= bits-1;
                }
            }
        }
        if ( !uncovered ) break;
        if ( pass == 0 ) continue;
        for ( v = 0; v < ni; ++v ) {
            if ( !scores[v] ) continue;
            if ( scores[v] > bestScore ) { best = v; bestScore = scores[v]; ties = 1; }
            else if ( scores[v] == bestScore && Decpla_Choose(state,++ties) == 0 ) best = v;
        }
        if ( best < 0 ) { fprintf(err,"decpla: no separating variable\n"); goto done; }
        keep[best/32] |= (word)1 << (2*(best%32));
    }
    for ( phase = 0; phase < 2; ++phase ) {
        Decpla_Cover_t * c = phase ? &f->On : &f->Off;
        for ( i = 0; i < c->nCubes; ++i ) for ( w = 0; w < nw; ++w )
            c->pData[i*nw+w] &= keep[w] | (keep[w] << 1);
    }
    ok = 1;
done:
    free(cache); free(tmp); free(keep); free(scores); return ok;
}
int Decpla_MinimizeSeeded( Decpla_Man_t * p, unsigned seed, size_t budget, FILE * err )
{
    int i;
    word state = seed;
    if ( !Decpla_Check(p,err) ) return 0;
    for ( i = 0; i < p->nOutputs; ++i )
        if ( !Decpla_Select(&p->pIsfs[i],p->nInputs,&state,budget,err) ) return 0;
    // Deterministic deletion prunes redundant selections and compacts covers.
    return Decpla_Minimize(p,err);
}
ABC_NAMESPACE_IMPL_END
