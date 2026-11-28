/**CFile****************************************************************

  FileName    [giaLutAbsorb.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Absorbs multi-fanout LUTs into all their fanout LUTs.]

  Author      [Longfei Fan]

***********************************************************************/

#include "gia.h"
#include "map/if/if.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Absorbs multi-fanout LUTs into all their fanout LUTs.]

  Description [A LUT u with 2..nFanoutMax LUT fanouts is removed from
  the mapping when every fanout's merged cut fits in nLutSize leaves.
  With a LUT library, the removal must also reduce the total LUT area.
  The AIG is not modified; only vMapping is rebuilt. Returns the number
  of removed LUTs; the total area gain is returned in pfAreaGain.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManLutAbsorb( Gia_Man_t * p, int nLutSize, int nFanoutMax, int nRounds, int fVerbose, If_LibLut_t * pLutLib, float * pfAreaGain )
{
    Vec_Wec_t * vLeaves, * vFanouts;
    Vec_Bit_t * vChanged, * vKeep;
    Vec_Int_t * vIds, * vFans, * vMerged, * vOld, * vMap;
    Vec_Int_t ** pvMerged;
    Gia_Obj_t * pObj;
    int nObjs = Gia_ManObjNum(p);
    int i, j, k, r, u, v, iFan, iLeaf, nFanouts, nRemoved, nTotal = 0, fOk;
    float Gain, GainRound, GainTotal = 0.0;

    if ( pfAreaGain )
        *pfAreaGain = 0.0;
    assert( Gia_ManHasMapping(p) );

    // collect LUT leaves and LUT-level fanouts
    vLeaves  = Vec_WecStart( nObjs );
    vFanouts = Vec_WecStart( nObjs );
    Gia_ManForEachLut( p, i )
        Gia_LutForEachFanin( p, i, iFan, k )
        {
            Vec_IntPush( Vec_WecEntry(vLeaves, i), iFan );
            Vec_WecPush( vFanouts, iFan, i );
        }

    // LUTs driving COs or buffers have to stay in the mapping
    vKeep = Vec_BitStart( nObjs );
    Gia_ManForEachCo( p, pObj, i )
        if ( Gia_ObjIsAndNotBuf(Gia_ObjFanin0(pObj)) )
            Vec_BitWriteEntry( vKeep, Gia_ObjFaninId0p(p, pObj), 1 );
    Gia_ManForEachBuf( p, pObj, i )
        if ( Gia_ObjIsAndNotBuf(Gia_ObjFanin0(pObj)) )
            Vec_BitWriteEntry( vKeep, Gia_ObjFaninId0p(p, pObj), 1 );
    vChanged = Vec_BitStart( nObjs );

    for ( r = 0; r < nRounds; r++ )
    {
        // snapshot the candidates, since LUTs disappear during the pass
        vIds = Vec_IntAlloc( nObjs );
        for ( i = 1; i < nObjs; i++ )
            if ( Vec_IntSize(Vec_WecEntry(vLeaves, i)) > 0 && Gia_ObjIsAndNotBuf(Gia_ManObj(p, i)) )
                Vec_IntPush( vIds, i );
        nRemoved = 0;
        GainRound = 0.0;
        Vec_IntForEachEntry( vIds, u, i )
        {
            Vec_Int_t * vLeavesU = Vec_WecEntry( vLeaves, u );
            if ( Vec_IntSize(vLeavesU) == 0 )
                continue;
            if ( Vec_BitEntry(vKeep, u) )
                continue;
            vFans = Vec_IntDup( Vec_WecEntry(vFanouts, u) );
            nFanouts = Vec_IntSize( vFans );
            if ( nFanouts < 2 || nFanouts > nFanoutMax )
            {
                Vec_IntFree( vFans );
                continue;
            }

            // build the merged cut of every fanout
            pvMerged = ABC_CALLOC( Vec_Int_t *, nFanouts );
            fOk = 1;
            Vec_IntForEachEntry( vFans, v, k )
            {
                vMerged = Vec_IntAlloc( Vec_IntSize(vLeavesU) + Vec_IntSize(Vec_WecEntry(vLeaves, v)) );
                Vec_IntForEachEntry( Vec_WecEntry(vLeaves, v), iLeaf, j )
                    if ( iLeaf != u )
                        Vec_IntPushUnique( vMerged, iLeaf );
                Vec_IntForEachEntry( vLeavesU, iLeaf, j )
                    Vec_IntPushUnique( vMerged, iLeaf );
                if ( Vec_IntSize(vMerged) > nLutSize )
                    fOk = 0;
                pvMerged[k] = vMerged;
            }

            // with a LUT library, require the removal to reduce total area
            Gain = 0.0;
            if ( fOk && pLutLib )
            {
                if ( Vec_IntSize(vLeavesU) > pLutLib->LutMax )
                    fOk = 0;
                else
                {
                    Gain = pLutLib->pLutAreas[Vec_IntSize(vLeavesU)];
                    Vec_IntForEachEntry( vFans, v, k )
                    {
                        if ( Vec_IntSize(Vec_WecEntry(vLeaves, v)) > pLutLib->LutMax ||
                             Vec_IntSize(pvMerged[k]) > pLutLib->LutMax )
                        {
                            fOk = 0;
                            break;
                        }
                        Gain += pLutLib->pLutAreas[Vec_IntSize(Vec_WecEntry(vLeaves, v))] -
                                pLutLib->pLutAreas[Vec_IntSize(pvMerged[k])];
                    }
                    if ( fOk && Gain <= 0.0 )
                        fOk = 0;
                }
            }

            if ( !fOk )
            {
                for ( k = 0; k < nFanouts; k++ )
                    if ( pvMerged[k] )
                        Vec_IntFree( pvMerged[k] );
                ABC_FREE( pvMerged );
                Vec_IntFree( vFans );
                continue;
            }

            // apply the absorption to every fanout
            for ( k = 0; k < nFanouts; k++ )
            {
                v = Vec_IntEntry( vFans, k );
                vMerged = pvMerged[k];
                vOld = Vec_WecEntry( vLeaves, v );
                Vec_IntForEachEntry( vMerged, iLeaf, j )
                    if ( iLeaf != u && Vec_IntFind(vOld, iLeaf) < 0 )
                        Vec_WecPush( vFanouts, iLeaf, v );
                Vec_IntRemove( Vec_WecEntry(vFanouts, u), v );
                Vec_IntClear( vOld );
                Vec_IntAppend( vOld, vMerged );
                Vec_BitWriteEntry( vChanged, v, 1 );
                Vec_IntFree( vMerged );
            }
            ABC_FREE( pvMerged );
            Vec_IntForEachEntry( vLeavesU, iLeaf, j )
                Vec_IntRemove( Vec_WecEntry(vFanouts, iLeaf), u );
            Vec_IntClear( vLeavesU );
            nRemoved++;
            GainRound += Gain;
            Vec_IntFree( vFans );
        }
        Vec_IntFree( vIds );
        if ( fVerbose )
        {
            if ( pLutLib )
                Abc_Print( 1, "Round %d: removed %d LUTs, area gain %.2f.\n", r + 1, nRemoved, GainRound );
            else
                Abc_Print( 1, "Round %d: removed %d LUTs.\n", r + 1, nRemoved );
        }
        nTotal += nRemoved;
        GainTotal += GainRound;
        if ( nRemoved == 0 )
            break;
    }

    // rebuild the mapping; leave derived data alone if nothing was removed
    if ( nTotal > 0 )
    {
        vMap = Vec_IntStart( nObjs );
        if ( Gia_ObjIsLut(p, 0) )
        {
            Vec_IntWriteEntry( vMap, 0, Vec_IntSize(vMap) );
            Vec_IntPush( vMap, Gia_ObjLutSize(p, 0) );
            for ( k = 0; k < Gia_ObjLutSize(p, 0); k++ )
                Vec_IntPush( vMap, Gia_ObjLutFanins(p, 0)[k] );
            Vec_IntPush( vMap, Gia_ObjLutFanins(p, 0)[Gia_ObjLutSize(p, 0)] );
        }
        for ( i = 1; i < nObjs; i++ )
        {
            Vec_Int_t * vLeavesI = Vec_WecEntry( vLeaves, i );
            if ( Vec_IntSize(vLeavesI) == 0 )
                continue;
            Vec_IntWriteEntry( vMap, i, Vec_IntSize(vMap) );
            Vec_IntPush( vMap, Vec_IntSize(vLeavesI) );
            Vec_IntForEachEntry( vLeavesI, iLeaf, j )
                Vec_IntPush( vMap, iLeaf );
            Vec_IntPush( vMap, Vec_BitEntry(vChanged, i) ? i :
                Gia_ObjLutFanins(p, i)[Gia_ObjLutSize(p, i)] );
        }
        Vec_IntFreeP( &p->vMapping );
        p->vMapping = vMap;
        Vec_IntFreeP( &p->vPacking );
        Vec_IntFreeP( &p->vCellMapping );
        Vec_IntFreeP( &p->vEdge1 );
        Vec_IntFreeP( &p->vEdge2 );
        Vec_WecFreeP( &p->vMapping2 );
        Vec_WecFreeP( &p->vFanouts2 );
    }
    Vec_WecFree( vLeaves );
    Vec_WecFree( vFanouts );
    Vec_BitFree( vChanged );
    Vec_BitFree( vKeep );
    if ( pfAreaGain )
        *pfAreaGain = GainTotal;
    return nTotal;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
