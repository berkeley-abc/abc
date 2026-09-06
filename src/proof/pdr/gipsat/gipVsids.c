/**************************************************************************************************
GipSAT -- C port of the GipSAT solver from the rIC3 model checker (https://github.com/gipsyh/rIC3),
ported from rIC3 v1.5.2-60-g4a97bec, src/gipsat/.
Copyright (C) 2023 - Present, Yuheng Su <gipsyh.icu@gmail.com>. All rights reserved.
Ported to C for ABC by Wish, 2026.

rIC3 is distributed under the GNU General Public License v3. This port is distributed as part of
ABC under the ABC license (see copyright.txt in the ABC root) with the explicit permission of the
rIC3 author.
**************************************************************************************************/

#include "gipsat.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

static void Gip_HeapInit( Gip_Heap_t * p, int nVarsAlloc )
{
    int i;
    p->vHeap = Vec_IntAlloc( 100 );
    p->pPos  = ABC_ALLOC( int, nVarsAlloc );
    for ( i = 0; i < nVarsAlloc; i++ )
        p->pPos[i] = -1;
}

static void Gip_HeapFree( Gip_Heap_t * p )
{
    Vec_IntFreeP( &p->vHeap );
    ABC_FREE( p->pPos );
}

void Gip_HeapClear( Gip_Heap_t * p )
{
    int i, v;
    Vec_IntForEachEntry( p->vHeap, v, i )
        p->pPos[v] = -1;
    Vec_IntClear( p->vHeap );
}

static void Gip_HeapUp( Gip_Heap_t * p, int Var, Gip_Act_t * pAct )
{
    int * pHeap = Vec_IntArray( p->vHeap );
    int idx = p->pPos[Var], pidx;
    if ( idx == -1 )
        return;
    while ( idx != 0 )
    {
        pidx = (idx - 1) >> 1;
        if ( pAct->pAct[pHeap[pidx]] >= pAct->pAct[Var] )
            break;
        pHeap[idx] = pHeap[pidx];
        p->pPos[pHeap[idx]] = idx;
        idx = pidx;
    }
    pHeap[idx] = Var;
    p->pPos[Var] = idx;
}

static void Gip_HeapDown( Gip_Heap_t * p, int idx, Gip_Act_t * pAct )
{
    int * pHeap = Vec_IntArray( p->vHeap );
    int nSize = Vec_IntSize( p->vHeap );
    int v = pHeap[idx];
    while ( 1 )
    {
        int left = 2*idx + 1, right, child;
        if ( left >= nSize )
            break;
        right = left + 1;
        child = ( right < nSize && pAct->pAct[pHeap[right]] > pAct->pAct[pHeap[left]] ) ? right : left;
        if ( pAct->pAct[v] >= pAct->pAct[pHeap[child]] )
            break;
        pHeap[idx] = pHeap[child];
        p->pPos[pHeap[idx]] = idx;
        idx = child;
    }
    pHeap[idx] = v;
    p->pPos[v] = idx;
}

static void Gip_HeapPush( Gip_Heap_t * p, int Var, Gip_Act_t * pAct )
{
    int idx;
    if ( p->pPos[Var] != -1 )
        return;
    idx = Vec_IntSize( p->vHeap );
    Vec_IntPush( p->vHeap, Var );
    p->pPos[Var] = idx;
    Gip_HeapUp( p, Var, pAct );
}

static int Gip_HeapPop( Gip_Heap_t * p, Gip_Act_t * pAct )
{
    int * pHeap, value;
    if ( Vec_IntSize(p->vHeap) == 0 )
        return -1;
    pHeap = Vec_IntArray( p->vHeap );
    value = pHeap[0];
    pHeap[0] = pHeap[Vec_IntSize(p->vHeap) - 1];
    p->pPos[pHeap[0]] = 0;
    p->pPos[value] = -1;
    Vec_IntPop( p->vHeap );
    if ( Vec_IntSize(p->vHeap) > 1 )
        Gip_HeapDown( p, 0, pAct );
    return value;
}

// number of significant bits of a 64-bit value (0 -> 0)
static inline int Gip_Bits64( word b )
{
    int n = 0;
    while ( b ) { n++; b >>= 1; }
    return n;
}

// bucket-table maintenance on first bump of a var: bucket_table[pos]
// approximates ceil(log2(pos+1)); one trailing entry (value = last + 1)
// serves vars that were never bumped
static void Gip_ActCheck( Gip_Act_t * p, int Var )
{
    if ( p->BktHeap.pPos[Var] == -1 )
    {
        word b;
        int blog;
        Gip_HeapPush( &p->BktHeap, Var, p );
        b = (word)(Vec_IntSize( p->vBktTable ) - 1);
        blog = Gip_Bits64( b );
        Vec_IntWriteEntry( p->vBktTable, Vec_IntSize(p->vBktTable) - 1, blog );
        Vec_IntPush( p->vBktTable, blog + 1 );
    }
    assert( p->BktHeap.pPos[Var] != -1 );
}

static int Gip_ActBucketOf( Gip_Act_t * p, int Var )
{
    int pos = p->BktHeap.pPos[Var];
    if ( pos == -1 )
        return Vec_IntEntryLast( p->vBktTable );
    return Vec_IntEntry( p->vBktTable, pos );
}

static void Gip_ActBump( Gip_Act_t * p, int Var, int nVarsAlloc )
{
    p->pAct[Var] += p->actInc;
    Gip_ActCheck( p, Var );
    Gip_HeapUp( &p->BktHeap, Var, p );
    if ( p->pAct[Var] > 1e100 )
    {
        int i;
        for ( i = 0; i < nVarsAlloc; i++ )
            p->pAct[i] *= 1e-100;
        p->actInc *= 1e-100;
    }
}

static void Gip_BucketEnsure( Gip_Bucket_t * p, int nBuckets )
{
    while ( Vec_PtrSize(p->vBuckets) < nBuckets )
        Vec_PtrPush( p->vBuckets, Vec_IntAlloc(16) );
}

static void Gip_BucketPush( Gip_Bucket_t * p, int Var, Gip_Act_t * pAct )
{
    int bucket;
    if ( p->pInBucket[Var] )
        return;
    bucket = Gip_ActBucketOf( pAct, Var );
    if ( p->head > bucket )
        p->head = bucket;
    Gip_BucketEnsure( p, bucket + 1 );
    Vec_IntPush( (Vec_Int_t *)Vec_PtrEntry(p->vBuckets, bucket), Var );
    p->pInBucket[Var] = 1;
}

static int Gip_BucketPop( Gip_Bucket_t * p )
{
    while ( p->head < Vec_PtrSize(p->vBuckets) )
    {
        Vec_Int_t * vB = (Vec_Int_t *)Vec_PtrEntry( p->vBuckets, p->head );
        if ( Vec_IntSize(vB) > 0 )
        {
            int Var = Vec_IntPop( vB );
            p->pInBucket[Var] = 0;
            return Var;
        }
        p->head++;
    }
    return -1;
}

void Gip_BucketClear( Gip_Bucket_t * p )
{
    int i;
    Vec_Int_t * vB;
    while ( p->head < Vec_PtrSize(p->vBuckets) )
    {
        vB = (Vec_Int_t *)Vec_PtrEntry( p->vBuckets, p->head );
        while ( Vec_IntSize(vB) > 0 )
            p->pInBucket[Vec_IntPop(vB)] = 0;
        p->head++;
    }
    Vec_PtrForEachEntry( Vec_Int_t *, p->vBuckets, vB, i )
        Vec_IntClear( vB );
    p->head = 0;
}

/**Function*************************************************************

  Synopsis    [Initializes the VSIDS state.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gip_VsidsInit( Gip_Vsids_t * p, int nVarsAlloc )
{
    p->Act.pAct = ABC_CALLOC( double, nVarsAlloc );
    p->Act.actInc = 1.0;
    Gip_HeapInit( &p->Act.BktHeap, nVarsAlloc );
    p->Act.vBktTable = Vec_IntAlloc( 100 );
    Vec_IntPush( p->Act.vBktTable, 0 );
    Gip_HeapInit( &p->Heap, nVarsAlloc );
    p->Bucket.vBuckets = Vec_PtrAlloc( 16 );
    Gip_BucketEnsure( &p->Bucket, 10 );
    p->Bucket.pInBucket = ABC_CALLOC( char, nVarsAlloc );
    p->Bucket.head = 0;
    p->fEnableBucket = 1;
    p->nVarsAlloc = nVarsAlloc;
}

void Gip_VsidsFree( Gip_Vsids_t * p )
{
    Vec_Int_t * vB;
    int i;
    ABC_FREE( p->Act.pAct );
    Gip_HeapFree( &p->Act.BktHeap );
    Vec_IntFreeP( &p->Act.vBktTable );
    Gip_HeapFree( &p->Heap );
    Vec_PtrForEachEntry( Vec_Int_t *, p->Bucket.vBuckets, vB, i )
        Vec_IntFree( vB );
    Vec_PtrFree( p->Bucket.vBuckets );
    ABC_FREE( p->Bucket.pInBucket );
}

void Gip_VsidsPush( Gip_Vsids_t * p, int Var )
{
    if ( p->fEnableBucket )
        Gip_BucketPush( &p->Bucket, Var, &p->Act );
    else
        Gip_HeapPush( &p->Heap, Var, &p->Act );
}

static int Gip_VsidsPop( Gip_Vsids_t * p )
{
    if ( p->fEnableBucket )
        return Gip_BucketPop( &p->Bucket );
    return Gip_HeapPop( &p->Heap, &p->Act );
}

void Gip_VsidsBump( Gip_Vsids_t * p, int Var )
{
    Gip_ActBump( &p->Act, Var, p->nVarsAlloc );
    if ( !p->fEnableBucket )
        Gip_HeapUp( &p->Heap, Var, &p->Act );
    Gip_BucketEnsure( &p->Bucket, Vec_IntEntryLast(p->Act.vBktTable) + 1 );
}

void Gip_VsidsDecay( Gip_Vsids_t * p )
{
    p->Act.actInc *= 1.0 / 0.95;
}

/**Function*************************************************************

  Synopsis    [Picks and assigns the next decision literal.]

  Description [Assigned vars popped from VSIDS are skipped. The phase of
  a var seen before is its saved phase; a never-assigned var gets FALSE.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gip_SolverDecide( Gip_Solver_t * p )
{
    int decide, Lit;
    while ( (decide = Gip_VsidsPop(&p->Vsids)) != -1 )
    {
        if ( p->pValue[decide] != GIP_NONE )
            continue;
        if ( p->pPhase[decide] != GIP_NONE )
            Lit = Gip_Lit( decide, p->pPhase[decide] == GIP_FALSE );
        else
            Lit = Gip_Lit( decide, 1 );
        Vec_IntPush( p->vPosInTrail, Vec_IntSize(p->vTrail) );
        Gip_SolverAssign( p, Lit, GIP_CREF_NONE );
        p->Stats.nDecisions++;
        return 1;
    }
    return 0;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
