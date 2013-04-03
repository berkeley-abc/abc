/**CFile****************************************************************

  FileName    [sfmNtk.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based optimization using internal don't-cares.]

  Synopsis    [Logic network.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: sfmNtk.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sfmInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Sfm_Ntk_t * Sfm_NtkAlloc( int nPis, int nPos, int nNodes, Vec_Int_t * vFanins, Vec_Int_t * vFanouts, Vec_Int_t * vEdges, Vec_Int_t * vOpts )
{
    Sfm_Ntk_t * p;
    Sfm_Obj_t * pObj, * pFan;
    int i, k, nObjSize, AddOn = 2;
    int nStructSize = sizeof(Sfm_Obj_t) / sizeof(int);
    int iFanin, iOffset = 2, iFanOffset = 0;
    int nEdges = Vec_IntSize(vEdges);
    int nObjs  = nPis + nPos + nNodes;
    int nSize  = 2 + nObjs * (nStructSize + 1) + 2 * nEdges + AddOn * (nPis + Vec_IntSum(vOpts));
    assert( sizeof(Sfm_Obj_t) % sizeof(int) == 0 );
    assert( nEdges == Vec_IntSum(vFanins) );
    assert( nEdges == Vec_IntSum(vFanouts) );
    p = ABC_CALLOC( Sfm_Ntk_t, 1 );
    p->pMem = ABC_CALLOC( int, nSize );
    for ( i = 0; i < nObjs; i++ )
    {
        Vec_IntPush( &p->vObjs, iOffset );
        pObj = Sfm_ManObj( p, i );
        pObj->Id  = i;
        if ( i < nPis )
        {
            pObj->Type = 1;
            assert( Vec_IntEntry(vFanins, i) == 0 );
            assert( Vec_IntEntry(vOpts, i) == 0 );
            Vec_IntPush( &p->vPis, iOffset );
        }
        else 
        {
            pObj->Type = 2;
            pObj->fOpt = Vec_IntEntry(vOpts, i);
            if ( i >= nPis + nNodes ) // PO
            {
                pObj->Type = 3;
                assert( Vec_IntEntry(vFanins, i) == 1 );
                assert( Vec_IntEntry(vFanouts, i) == 0 );
                assert( Vec_IntEntry(vOpts, i) == 0 );
                Vec_IntPush( &p->vPos, iOffset );
            }
            for ( k = 0; k < Vec_IntEntry(vFanins, i); k++ )
            {
                iFanin = Vec_IntEntry( vEdges, iFanOffset++ );
                pFan = Sfm_ManObj( p, iFanin );
                assert( iFanin < i );
                pObj->Fanio[ pObj->nFanis++ ] = iFanin;
                pFan->Fanio[ pFan->nFanis + pFan->nFanos++ ] = i;
            }
        }
        // add node size
        nObjSize  = nStructSize + Vec_IntEntry(vFanins, i) + Vec_IntEntry(vFanouts, i) + AddOn * (pObj->Type==1 || pObj->fOpt);
        nObjSize += (int)( nObjSize & 1 );
        assert( (nObjSize & 1) == 0 );
        iOffset  += nObjSize;
    }
    assert( iOffset <= nSize );
    assert( iFanOffset == Vec_IntSize(vEdges) );
    iFanOffset = 0;
    Sfm_ManForEachObj( p, pObj, i )
    {
        assert( Vec_IntEntry(vFanins, i)  == (int)pObj->nFanis );
        assert( Vec_IntEntry(vFanouts, i) == (int)pObj->nFanos );
        for ( k = 0; k < (int)pObj->nFanis; k++ )
            assert( pObj->Fanio[k] == Vec_IntEntry(vEdges, iFanOffset++) );
    }
    assert( iFanOffset == Vec_IntSize(vEdges) );
    return p;
}
void Sfm_NtkFree( Sfm_Ntk_t * p )
{
    ABC_FREE( p->pMem );
    ABC_FREE( p->vObjs.pArray );
    ABC_FREE( p->vPis.pArray );
    ABC_FREE( p->vPos.pArray );
    ABC_FREE( p->vMem.pArray );
    ABC_FREE( p->vLevels.pArray );
    ABC_FREE( p->vTravIds.pArray );
    ABC_FREE( p->vSatVars.pArray );
    ABC_FREE( p->vTruths.pArray );
    ABC_FREE( p );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

