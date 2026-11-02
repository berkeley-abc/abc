/**CFile****************************************************************

  FileName    [giaEdit.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [GIA import, metadata and export for the mutable editing kernel.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaEdit.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "giaEdit.h"
#include "misc/tim/tim.h"
#include <limits.h>

ABC_NAMESPACE_IMPL_START

/**Function*************************************************************

  Synopsis    [Bounds allocations and signed literal indices.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gie_ObjectLimit( void )
{
    size_t Limit = Abc_MinInt( INT_MAX / 2, GIA_NONE );
    if ( Limit > ~(size_t) 0 / sizeof( Gie_Obj_t ) ) Limit = ~(size_t) 0 / sizeof( Gie_Obj_t );
    if ( Limit > ~(size_t) 0 / sizeof( Gie_Fan_t ) ) Limit = ~(size_t) 0 / sizeof( Gie_Fan_t );
    return (int) Limit;
}

/**Function*************************************************************

  Synopsis    [Computes XAIG input levels from the timing manager.]

  Description [Recomputes box-aware levels because the incoming level
  vector may contain plain AIG levels. A temporary view puts register
  outputs before box outputs for the shared level computation, reversing
  Gia_ManDupNormalize's CI permutation. The returned levels follow the
  original CI order. Barrier buffers are rejected at entry.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gie_BoxCiLevels( Gia_Man_t * pGia )
{
    Gia_Man_t * pLevels = pGia;
    Gia_Obj_t * pObj;
    Tim_Man_t * pTim = (Tim_Man_t *) pGia->pManTime;
    Vec_Int_t *vLevels, *vResult;
    int nRegs = Gia_ManRegNum( pGia );
    int fShuffle = nRegs && Gia_ManIsNormalized( pGia );
    int i, iCi, nCis = Gia_ManCiNum( pGia ), nPis = Tim_ManPiNum( pTim ) - nRegs;
    assert( Gia_ManBufNum( pGia ) == 0 );
    if ( nRegs )
    {
        pLevels = Gia_ManStart( Gia_ManObjNum( pGia ) );
        // Preserve equal-fanin ANDs and their levels in simple GIAs.
        pLevels->fGiaSimple = 1;
        Gia_ManConst0( pGia )->Value = 0;
        for ( i = 0; i < nCis; i++ )
        {
            iCi = !fShuffle || i < nPis ? i : i < nPis + nRegs ? nCis - nRegs + i - nPis : i - nRegs;
            Gia_ManCi( pGia, iCi )->Value = Gia_ManAppendCi( pLevels );
        }
        Gia_ManForEachAnd ( pGia, pObj, i )
            pObj->Value = Gia_ManAppendAnd( pLevels, Gia_ObjFanin0Copy( pObj ), Gia_ObjFanin1Copy( pObj ) );
        Gia_ManForEachCo ( pGia, pObj, i )
            Gia_ManAppendCo( pLevels, Gia_ObjFanin0Copy( pObj ) );
        pLevels->pManTime = pTim;
        pLevels->nAnd2Delay = pGia->nAnd2Delay;
    }
    Gia_ManLevelWithBoxes( pLevels );
    vLevels = Gia_ManGetCiLevels( pLevels );
    if ( pLevels != pGia )
    {
        pLevels->pManTime = NULL;
        Gia_ManStop( pLevels );
    }
    if ( !fShuffle ) return vLevels;
    vResult = Vec_IntAlloc( Vec_IntSize( vLevels ) );
    for ( i = 0; i < nPis; i++ )
        Vec_IntPush( vResult, Vec_IntEntry( vLevels, i ) );
    for ( i = nPis + nRegs; i < Vec_IntSize( vLevels ); i++ )
        Vec_IntPush( vResult, Vec_IntEntry( vLevels, i ) );
    for ( i = nPis; i < nPis + nRegs; i++ )
        Vec_IntPush( vResult, Vec_IntEntry( vLevels, i ) );
    Vec_IntFree( vLevels );
    return vResult;
}

/**Function*************************************************************

  Synopsis    [Imports a GIA and computes initial levels and required levels.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gie_ManStart( Gie_Man_t * p, Gia_Man_t * pGia, int fKeepLevel, int HashMode, Vec_Int_t * vCiLevels )
{
    Gia_Obj_t * pObj;
    int i;
    memset( p, 0, sizeof( Gie_Man_t ) );
    p->fHashAll = HashMode == GIE_HASH_ALL;
    p->nObjLimit = Gie_ObjectLimit();
    p->nCap = Abc_MinInt( p->nObjLimit, Abc_MaxInt( 16, 2 * Gia_ManObjNum( pGia ) ) );
    p->pObjs = ABC_ALLOC( Gie_Obj_t, p->nCap );
    p->pFans = ABC_ALLOC( Gie_Fan_t, p->nCap );
    p->nHashMask = 16;
    while ( p->nHashMask < Gia_ManObjNum( pGia ) )
        p->nHashMask *= 2;
    p->pHash = ABC_CALLOC( int, p->nHashMask );
    p->nHashMask--;
    p->vCis = Vec_IntAlloc( Gia_ManCiNum( pGia ) );
    p->vCos = Vec_IntAlloc( Gia_ManCoNum( pGia ) );
    p->vStack = Vec_IntAlloc( GIE_STACK_INITIAL );
    p->vOrder = Vec_IntAlloc( p->nCap );
    p->vPromote = p->fHashAll ? Vec_IntAlloc( 128 ) : NULL;
    p->fKeepLevel = fKeepLevel;
    p->iRoot = -1;
    p->nObjs = Gia_ManObjNum( pGia );
    memset( p->pObjs, 0, sizeof( Gie_Obj_t ) * p->nObjs );
    memset( p->pFans, 0, sizeof( Gie_Fan_t ) * p->nObjs );
    p->pObjs[0].Type = GIE_CONST;
    p->pObjs[0].Handled = 1;
    p->pFans[0].Required = ABC_INFINITY;
    Gia_ManForEachObj1 ( pGia, pObj, i )
    {
        Gie_Obj_t * pNode = p->pObjs + i;
        p->pFans[i].Required = ABC_INFINITY;
        if ( Gia_ObjIsCi( pObj ) )
        {
            pNode->Type = GIE_CI;
            pNode->Handled = 1;
            if ( vCiLevels ) pNode->Level = Vec_IntEntry( vCiLevels, Gia_ObjCioId( pObj ) );
        }
        else if ( Gia_ObjIsCo( pObj ) )
        {
            pNode->Type = GIE_CO;
            pNode->Fan[0] = Gia_ObjFaninLit0( pObj, i );
            Gie_Link( p, i, 0 );
            p->nLevelMax = Abc_MaxInt( p->nLevelMax, p->pObjs[pNode->Fan[0] >> 1].Level );
        }
        else
        {
            assert( Gia_ObjIsAnd( pObj ) );
            pNode->Type = GIE_AND;
            pNode->Fan[0] = Gia_ObjFaninLit0( pObj, i );
            pNode->Fan[1] = Gia_ObjFaninLit1( pObj, i );
            pNode->Level = 1 + Abc_MaxInt( p->pObjs[pNode->Fan[0] >> 1].Level, p->pObjs[pNode->Fan[1] >> 1].Level );
            Gie_Link( p, i, 0 );
            Gie_Link( p, i, 1 );
            p->nAnds++;
            if ( HashMode != GIE_HASH_DEFER ) Gie_Ready( p, i );
        }
    }
    Gia_ManForEachCi ( pGia, pObj, i )
        Vec_IntPush( p->vCis, Gia_ObjId( pGia, pObj ) );
    Gia_ManForEachCo ( pGia, pObj, i )
        Vec_IntPush( p->vCos, Gia_ObjId( pGia, pObj ) );
    p->nOrig = p->nObjs;
    // Refactoring never adds a dependency between unhandled original nodes.
    // Their remaining fanout paths keep these required levels valid for
    // the whole pass. Forward levels are refreshed only when needed.
    for ( i = p->nObjs - 1; i > 0; i-- )
    {
        Gie_Obj_t * pNode = p->pObjs + i;
        if ( pNode->Type == GIE_CO )
        {
            // Fixed XAIG input arrivals are upper bounds only if each
            // interface output keeps its original arrival bound as well.
            p->pFans[i].Required = vCiLevels ? p->pObjs[pNode->Fan[0] >> 1].Level : p->nLevelMax;
            p->pFans[pNode->Fan[0] >> 1].Required =
                Abc_MinInt( p->pFans[pNode->Fan[0] >> 1].Required, p->pFans[i].Required );
        }
        else if ( pNode->Type == GIE_AND )
        {
            int k;
            if ( pNode->Refs == 0 )
            {
                Gie_Delete( p, i );
                continue;
            }
            for ( k = 0; k < 2; k++ )
            {
                int Var = pNode->Fan[k] >> 1;
                p->pFans[Var].Required = Abc_MinInt( p->pFans[Var].Required, p->pFans[i].Required - 1 );
            }
        }
    }
}

/**Function*************************************************************

  Synopsis    [Releases the kernel while leaving the owning pass intact.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gie_ManStop( Gie_Man_t * p )
{
    Vec_IntFree( p->vCis );
    Vec_IntFree( p->vCos );
    Vec_IntFree( p->vStack );
    Vec_IntFree( p->vOrder );
    Vec_IntFreeP( &p->vPromote );
    ABC_FREE( p->pObjs );
    ABC_FREE( p->pFans );
    ABC_FREE( p->pHash );
}

/**Function*************************************************************

  Synopsis    [Copies interface metadata, including an empty vector.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Gie_DupVector( Vec_Int_t * pVec )
{
    return Vec_IntSize( pVec ) ? Vec_IntDup( pVec ) : Vec_IntAlloc( 0 );
}

/**Function*************************************************************

  Synopsis    [Duplicates interface, sequential and timing metadata into a fresh GIA.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gie_ManDupMetadata( Gia_Man_t * pNew, Gia_Man_t * pOld )
{
    Gia_ManSetRegNum( pNew, Gia_ManRegNum( pOld ) );
    pNew->nConstrs = pOld->nConstrs;
    if ( pOld->vRegInits ) pNew->vRegInits = Gie_DupVector( pOld->vRegInits );
    if ( pOld->vRegClasses ) pNew->vRegClasses = Gie_DupVector( pOld->vRegClasses );
    if ( pOld->vFlopClasses ) pNew->vFlopClasses = Gie_DupVector( pOld->vFlopClasses );
    if ( pOld->vNamesIn ) pNew->vNamesIn = Vec_PtrDupStr( pOld->vNamesIn );
    if ( pOld->vNamesOut ) pNew->vNamesOut = Vec_PtrDupStr( pOld->vNamesOut );
    if ( pOld->vUserPiIds ) pNew->vUserPiIds = Gie_DupVector( pOld->vUserPiIds );
    if ( pOld->vUserPoIds ) pNew->vUserPoIds = Gie_DupVector( pOld->vUserPoIds );
    if ( pOld->vUserFfIds ) pNew->vUserFfIds = Gie_DupVector( pOld->vUserFfIds );
    if ( pOld->pManTime ) pNew->pManTime = Tim_ManDup( (Tim_Man_t *) pOld->pManTime, 0 );
    if ( pOld->pAigExtra ) pNew->pAigExtra = Gia_ManDup( pOld->pAigExtra );
    if ( pOld->vCiArrs ) pNew->vCiArrs = Gie_DupVector( pOld->vCiArrs );
    if ( pOld->vCoReqs ) pNew->vCoReqs = Gie_DupVector( pOld->vCoReqs );
    if ( pOld->vCoArrs ) pNew->vCoArrs = Gie_DupVector( pOld->vCoArrs );
    if ( pOld->vCoAttrs ) pNew->vCoAttrs = Gie_DupVector( pOld->vCoAttrs );
    if ( pOld->vInArrs ) pNew->vInArrs = Vec_FltSize( pOld->vInArrs ) ? Vec_FltDup( pOld->vInArrs ) : Vec_FltAlloc( 0 );
    if ( pOld->vOutReqs )
        pNew->vOutReqs = Vec_FltSize( pOld->vOutReqs ) ? Vec_FltDup( pOld->vOutReqs ) : Vec_FltAlloc( 0 );
    pNew->DefInArrs = pOld->DefInArrs;
    pNew->DefOutReqs = pOld->DefOutReqs;
    pNew->And2Delay = pOld->And2Delay;
    pNew->nAnd2Delay = pOld->nAnd2Delay;
}

/**Function*************************************************************

  Synopsis    [Exports the handled topological order as a normalized GIA.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gie_ManExport( Gie_Man_t * p, Gia_Man_t * pOld )
{
    Gia_Man_t * pNew = Gia_ManStart( p->nAnds + Vec_IntSize( p->vCis ) + Vec_IntSize( p->vCos ) + 1 );
    int * pCopies = ABC_ALLOC( int, p->nObjs );
    int i, Id, Lit;
    memset( pCopies, 0xFF, p->nObjs * sizeof( int ) );
    pCopies[0] = 0;
    pNew->pName = Abc_UtilStrsav( pOld->pName );
    pNew->pSpec = Abc_UtilStrsav( pOld->pSpec );
    // The exact output capacity is known. Fill a fresh GIA directly;
    // optional append-time managers are absent on this private result.
    Vec_IntFill( pNew->vCis, Vec_IntSize( p->vCis ), 0 );
    Vec_IntFill( pNew->vCos, Vec_IntSize( p->vCos ), 0 );
    Vec_IntForEachEntry ( p->vCis, Id, i )
    {
        int NewId = pNew->nObjs++;
        Gia_Obj_t * pObj = pNew->pObjs + NewId;
        pObj->fTerm = 1;
        pObj->iDiff0 = GIA_NONE;
        pObj->iDiff1 = i;
        Vec_IntWriteEntry( pNew->vCis, i, NewId );
        pCopies[Id] = 2 * NewId;
    }
    // The handled-node vector is already topological. Stable IDs let dead
    // entries remain until export without maintaining a second linked list.
    Vec_IntForEachEntry ( p->vOrder, Id, i )
    {
        int a, b, NewId;
        Gia_Obj_t * pObj;
        if ( p->pObjs[Id].Type != GIE_AND || !p->pObjs[Id].Refs ) continue;
        a = p->pObjs[Id].Fan[0];
        b = p->pObjs[Id].Fan[1];
        assert( pCopies[a >> 1] >= 0 && pCopies[b >> 1] >= 0 );
        a = pCopies[a >> 1] ^ ( a & 1 );
        b = pCopies[b >> 1] ^ ( b & 1 );
        if ( a > b ) ABC_SWAP( int, a, b );
        NewId = pNew->nObjs++;
        assert( ( a >> 1 ) != ( b >> 1 ) && ( b >> 1 ) < NewId );
        pObj = pNew->pObjs + NewId;
        pObj->iDiff0 = NewId - ( a >> 1 );
        pObj->iDiff1 = NewId - ( b >> 1 );
        pObj->fCompl0 = a & 1;
        pObj->fCompl1 = b & 1;
        pCopies[Id] = 2 * NewId;
    }
    Vec_IntForEachEntry ( p->vCos, Id, i )
    {
        int NewId = pNew->nObjs++;
        Gia_Obj_t * pObj = pNew->pObjs + NewId;
        Lit = p->pObjs[Id].Fan[0];
        assert( pCopies[Lit >> 1] >= 0 );
        assert( !p->fKeepLevel || p->pObjs[Lit >> 1].Level <= p->pFans[Id].Required );
        Lit = pCopies[Lit >> 1] ^ ( Lit & 1 );
        pObj->fTerm = 1;
        pObj->iDiff0 = NewId - ( Lit >> 1 );
        pObj->fCompl0 = Lit & 1;
        pObj->iDiff1 = i;
        Vec_IntWriteEntry( pNew->vCos, i, NewId );
    }
    assert( pNew->nObjs == p->nAnds + Vec_IntSize( p->vCis ) + Vec_IntSize( p->vCos ) + 1 );
    Gie_ManDupMetadata( pNew, pOld );
    ABC_FREE( pCopies );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Fingerprints the original fanin and fanout neighborhoods.]

  Description [The deterministic colors guide search effort and select recipe lists.
  They never justify a replacement or establish functional equivalence.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Gie_Neighborhoods( Gie_Man_t * p, int nObjs, int Rounds )
{
    unsigned *A = ABC_ALLOC( unsigned, nObjs ), *B = ABC_ALLOC( unsigned, nObjs ), a, b;
    int i, r, x, y;
    for ( i = 0; i < nObjs; i++ )
        A[i] = Gie_MixColor( p->pObjs[i].Type + 17u * (unsigned) p->pObjs[i].Refs );
    for ( r = 0; r < Rounds; r++ )
    {
        memset( B, 0, sizeof( unsigned ) * nObjs );
        for ( i = 0; i < nObjs; i++ )
        {
            B[i] += Gie_MixColor( A[i] );
            if ( p->pObjs[i].Type != GIE_AND && p->pObjs[i].Type != GIE_CO ) continue;
            x = p->pObjs[i].Fan[0];
            a = Gie_MixColor( A[x >> 1] ^ ( ( x & 1 ) * 0x55555555u ) );
            B[x >> 1] += Gie_MixColor( A[i] ^ ( ( x & 1 ) * 0x33333333u ) );
            if ( p->pObjs[i].Type == GIE_CO )
            {
                B[i] += a;
                continue;
            }
            y = p->pObjs[i].Fan[1];
            b = Gie_MixColor( A[y >> 1] ^ ( ( y & 1 ) * 0x55555555u ) );
            B[y >> 1] += Gie_MixColor( A[i] ^ ( ( y & 1 ) * 0x33333333u ) );
            B[i] += a + b + Gie_MixColor( a ^ b );
        }
        ABC_SWAP( unsigned *, A, B );
    }
    ABC_FREE( B );
    return A;
}

ABC_NAMESPACE_IMPL_END
