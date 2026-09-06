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

/**Function*************************************************************

  Synopsis    [Creates the shared GipSAT context.]

  Description [Derives a full static CNF over the entire AIG and builds
  the CSR dependency table dep(v) = variables appearing in the defining
  clauses of v. Shared read-only by all frame solvers.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gip_Ctx_t * Gip_CtxCreate( Aig_Man_t * pAig, Cnf_Man_t * pCnfMan )
{
    Gip_Ctx_t * p;
    int * pStamp;   // per-var stamp for dedup while collecting deps
    int * pCount;   // per-var dep count (pass 1)
    int ObjId, i, c, w, u, nObjs;
    int * pLit, * pStop;
    p = ABC_CALLOC( Gip_Ctx_t, 1 );
    p->pAig  = pAig;
    p->pCnf  = Cnf_DeriveOtherWithMan( pCnfMan, pAig, 0 );
    p->nVars = p->pCnf->nVars;
    assert( p->nVars == Aig_ManObjNumMax(pAig) );
    p->varConst = Gip_ObjVar( Aig_ManConst1(pAig) );
    assert( p->varConst >= 0 && p->varConst < p->nVars );
    nObjs = Aig_ManObjNumMax( pAig );

    // pass 1: count deps per defined var
    pCount = ABC_CALLOC( int, p->nVars );
    pStamp = ABC_ALLOC( int, p->nVars );
    for ( i = 0; i < p->nVars; i++ )
        pStamp[i] = -1;
    for ( ObjId = 0; ObjId < nObjs; ObjId++ )
    {
        if ( p->pCnf->pObj2Count[ObjId] <= 0 )
            continue;
        w = ObjId;
        for ( c = p->pCnf->pObj2Clause[ObjId]; c < p->pCnf->pObj2Clause[ObjId] + p->pCnf->pObj2Count[ObjId]; c++ )
            for ( pLit = p->pCnf->pClauses[c], pStop = p->pCnf->pClauses[c+1]; pLit < pStop; pLit++ )
            {
                u = Gip_LitVar( *pLit );
                if ( u == w || pStamp[u] == ObjId )
                    continue;
                pStamp[u] = ObjId;
                pCount[w]++;
            }
    }
    // build offsets
    p->pDepOffset = ABC_ALLOC( int, p->nVars + 1 );
    p->pDepOffset[0] = 0;
    for ( i = 0; i < p->nVars; i++ )
        p->pDepOffset[i+1] = p->pDepOffset[i] + pCount[i];
    p->nDepData = p->pDepOffset[p->nVars];
    p->pDepData = ABC_ALLOC( int, Abc_MaxInt(p->nDepData, 1) );
    // pass 2: fill
    memset( pCount, 0, sizeof(int) * p->nVars );
    for ( i = 0; i < p->nVars; i++ )
        pStamp[i] = -1;
    for ( ObjId = 0; ObjId < nObjs; ObjId++ )
    {
        if ( p->pCnf->pObj2Count[ObjId] <= 0 )
            continue;
        w = ObjId;
        for ( c = p->pCnf->pObj2Clause[ObjId]; c < p->pCnf->pObj2Clause[ObjId] + p->pCnf->pObj2Count[ObjId]; c++ )
            for ( pLit = p->pCnf->pClauses[c], pStop = p->pCnf->pClauses[c+1]; pLit < pStop; pLit++ )
            {
                u = Gip_LitVar( *pLit );
                if ( u == w || pStamp[u] == ObjId )
                    continue;
                pStamp[u] = ObjId;
                p->pDepData[ p->pDepOffset[w] + pCount[w]++ ] = u;
            }
    }
    ABC_FREE( pStamp );
    ABC_FREE( pCount );
    return p;
}

/**Function*************************************************************

  Synopsis    [Frees the context.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gip_CtxFree( Gip_Ctx_t * p )
{
    if ( p == NULL )
        return;
    Cnf_DataFree( p->pCnf );
    ABC_FREE( p->pDepOffset );
    ABC_FREE( p->pDepData );
    ABC_FREE( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
