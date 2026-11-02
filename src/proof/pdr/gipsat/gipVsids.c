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

  Description [The hot operations (push, pop, bump, decide) are inlined
  in gipsat.h.]

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

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
