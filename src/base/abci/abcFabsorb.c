/**CFile****************************************************************

  FileName    [abcFabsorb.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Absorbs multi-fanout LUTs into all their fanout LUTs.]

  Author      [longfei]

***********************************************************************/

#include "base/abc/abc.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes the fanins of v after absorbing u into it.]

  Description [The result is (fanins(v) minus u) plus fanins(u), without
  duplicates. The returned vector must be freed by the caller.]

***********************************************************************/
static Vec_Ptr_t * Abc_FabsorbMergedFanins( Abc_Obj_t * pU, Abc_Obj_t * pV )
{
    Vec_Ptr_t * vRes = Vec_PtrAlloc( Abc_ObjFaninNum(pU) + Abc_ObjFaninNum(pV) );
    Abc_Obj_t * pFanin;
    int j;
    Abc_ObjForEachFanin( pV, pFanin, j )
        if ( pFanin != pU )
            Vec_PtrPushUnique( vRes, pFanin );
    Abc_ObjForEachFanin( pU, pFanin, j )
        Vec_PtrPushUnique( vRes, pFanin );
    return vRes;
}

/**Function*************************************************************

  Synopsis    [Composes the function of u into the function of v.]

  Description [Variable i of a node function is its i-th fanin. The variable
  of v that stands for u is moved to a spare variable S and then replaced by
  the function of u, both expressed over the merged fanin list vNew.]

***********************************************************************/
static Hop_Obj_t * Abc_FabsorbFunction( Hop_Man_t * pMan, Abc_Obj_t * pU, Abc_Obj_t * pV, Vec_Ptr_t * vNew )
{
    Hop_Obj_t * pFuncV, * pFuncU;
    Abc_Obj_t * pFanin;
    int * pPerm;
    int j, nSpare = Vec_PtrSize(vNew);

    Hop_IthVar( pMan, nSpare );

    pPerm = ABC_ALLOC( int, Abc_ObjFaninNum(pV) );
    Abc_ObjForEachFanin( pV, pFanin, j )
        pPerm[j] = (pFanin == pU) ? nSpare : Vec_PtrFind( vNew, pFanin );
    pFuncV = Hop_Permute( pMan, (Hop_Obj_t *)pV->pData, Abc_ObjFaninNum(pV), pPerm );
    ABC_FREE( pPerm );

    pPerm = ABC_ALLOC( int, Abc_ObjFaninNum(pU) );
    Abc_ObjForEachFanin( pU, pFanin, j )
        pPerm[j] = Vec_PtrFind( vNew, pFanin );
    pFuncU = Hop_Permute( pMan, (Hop_Obj_t *)pU->pData, Abc_ObjFaninNum(pU), pPerm );
    ABC_FREE( pPerm );

    return Hop_Compose( pMan, pFuncV, pFuncU, nSpare );
}

/**Function*************************************************************

  Synopsis    [Tries to absorb node u into all its fanouts and delete it.]

  Description [Returns 1 if u was removed. The network is not touched unless
  every fanout stays within nLutSize fanins.]

***********************************************************************/
static int Abc_FabsorbNode( Abc_Ntk_t * pNtk, Abc_Obj_t * pU, int nLutSize, int nFanoutMax )
{
    Hop_Man_t * pMan = (Hop_Man_t *)pNtk->pManFunc;
    Vec_Ptr_t * vFanouts, * vFanins;
    Vec_Ptr_t ** pvNew;
    Hop_Obj_t ** pFuncs;
    Abc_Obj_t * pV, * pFanin;
    int i, k, nFanouts, fOk = 1;

    if ( !Abc_ObjIsNode(pU) || pU->pData == NULL )
        return 0;
    nFanouts = Abc_ObjFanoutNum( pU );
    if ( nFanouts < 2 || nFanouts > nFanoutMax )
        return 0;

    // all fanouts must be LUT nodes
    vFanouts = Vec_PtrAlloc( nFanouts );
    Abc_ObjForEachFanout( pU, pV, i )
    {
        if ( !Abc_ObjIsNode(pV) || pV->pData == NULL )
        {
            Vec_PtrFree( vFanouts );
            return 0;
        }
        Vec_PtrPush( vFanouts, pV );
    }

    // every absorbed fanout must still fit into a K-input LUT
    pvNew = ABC_CALLOC( Vec_Ptr_t *, nFanouts );
    for ( i = 0; i < nFanouts; i++ )
    {
        pvNew[i] = Abc_FabsorbMergedFanins( pU, (Abc_Obj_t *)Vec_PtrEntry(vFanouts, i) );
        if ( Vec_PtrSize(pvNew[i]) > nLutSize )
        {
            fOk = 0;
            break;
        }
    }

    if ( fOk )
    {
        pFuncs = ABC_ALLOC( Hop_Obj_t *, nFanouts );
        for ( i = 0; i < nFanouts; i++ )
            pFuncs[i] = Abc_FabsorbFunction( pMan, pU, (Abc_Obj_t *)Vec_PtrEntry(vFanouts, i), pvNew[i] );
        for ( i = 0; i < nFanouts; i++ )
        {
            pV = (Abc_Obj_t *)Vec_PtrEntry( vFanouts, i );
            vFanins = pvNew[i];
            Abc_ObjRemoveFanins( pV );
            Vec_PtrForEachEntry( Abc_Obj_t *, vFanins, pFanin, k )
                Abc_ObjAddFanin( pV, pFanin );
            pV->pData = pFuncs[i];
        }
        ABC_FREE( pFuncs );
        Abc_NtkDeleteObj( pU );
    }

    for ( i = 0; i < nFanouts; i++ )
        if ( pvNew[i] )
            Vec_PtrFree( pvNew[i] );
    ABC_FREE( pvNew );
    Vec_PtrFree( vFanouts );
    return fOk;
}

/**Function*************************************************************

  Synopsis    [Absorbs multi-fanout LUTs into all their fanouts.]

  Description [A node u with 2..nFanoutMax fanouts, all of which are LUTs,
  is deleted when every fanout still has at most nLutSize fanins after
  u is absorbed into it. Runs up to nRounds passes. Returns the number of
  removed nodes.]

***********************************************************************/
int Abc_NtkFabsorb( Abc_Ntk_t * pNtk, int nLutSize, int nFanoutMax, int nRounds, int fVerbose )
{
    Vec_Int_t * vIds;
    Abc_Obj_t * pObj;
    int i, r, nRemoved, nTotal = 0;

    assert( Abc_NtkIsLogic(pNtk) && Abc_NtkHasAig(pNtk) );
    for ( r = 0; r < nRounds; r++ )
    {
        // snapshot ids: nodes are deleted while iterating
        vIds = Vec_IntAlloc( Abc_NtkObjNumMax(pNtk) );
        Abc_NtkForEachNode( pNtk, pObj, i )
            Vec_IntPush( vIds, Abc_ObjId(pObj) );
        nRemoved = 0;
        for ( i = 0; i < Vec_IntSize(vIds); i++ )
        {
            pObj = Abc_NtkObj( pNtk, Vec_IntEntry(vIds, i) );
            if ( pObj && Abc_FabsorbNode( pNtk, pObj, nLutSize, nFanoutMax ) )
                nRemoved++;
        }
        Vec_IntFree( vIds );
        if ( fVerbose )
            Abc_Print( 1, "Round %d: removed %d nodes.\n", r + 1, nRemoved );
        nTotal += nRemoved;
        if ( nRemoved == 0 )
            break;
    }
    return nTotal;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
