/**CFile****************************************************************

  FileName    [drwSat.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Compact DAG-aware AIG rewriting.]

  Synopsis    [Fast combinational optimization for verification.]

  Author      [OpenAI Codex, with Alan Mishchenko]

  Affiliation [ABC project]

  Date        [Ver. 1.0. Started - November 9, 2026.]

  Revision    [$Id: drwSat.c,v 1.00 2026/11/09 00:00:00 Exp $]

***********************************************************************/

#include "drw.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Reimplements the drwsat rewrite/refactor/rewrite script.]

  Description [Uses the compact DRW and DRF engines without level
  constraints. Balancing is optional and disabled by the caller by default.
  The transition relation and CI/CO order are preserved. The input remains
  owned by the caller; NULL reports unsupported input or a failed pass.]

  SideEffects [May modify scratch fields of the input graph.]

  SeeAlso     [Dar_ManRwsat]

***********************************************************************/
Gia_Man_t * Drw_ManRwsat( Gia_Man_t * pGia, int fBalance, int fVerbose )
{
    return Drw_ManRwsatWithStop( pGia, fBalance, fVerbose, NULL, NULL );
}

/**Function*************************************************************

  Synopsis    [Runs the verification rewrite script with cooperative cancellation.]

  Description [Only completed passes can be returned. A stop discards all
  private work and leaves the input owned by the caller.]

  SideEffects []

  SeeAlso     [Drw_ManRwsat]

***********************************************************************/
Gia_Man_t * Drw_ManRwsatWithStop( Gia_Man_t * pGia, int fBalance, int fVerbose,
    int (*pFuncStop)(void *), void * pStopData )
{
    Gia_Man_t * pWork, * pNext;
    int Pass;
    if ( !pGia || Gia_ManHasChoices(pGia) || pGia->pMuxes ||
         Gia_ManXorNum(pGia) || Gia_ManBufNum(pGia) || Gia_ManBoxNum(pGia) )
        return NULL;
    if ( pFuncStop && pFuncStop(pStopData) ) return NULL;
    pWork = Gia_ManDup( pGia );
    pWork->nConstrs = pGia->nConstrs;
    if ( pGia->vRegInits ) pWork->vRegInits = Vec_IntDup( pGia->vRegInits );
    if ( pGia->vNamesIn ) pWork->vNamesIn = Vec_PtrDupStr( pGia->vNamesIn );
    if ( pGia->vNamesOut ) pWork->vNamesOut = Vec_PtrDupStr( pGia->vNamesOut );
    for ( Pass = 0; Pass < 3; Pass++ )
    {
        if ( pFuncStop && pFuncStop(pStopData) ) { Gia_ManStop(pWork); return NULL; }
        if ( fBalance && Pass != 1 )
        {
            pNext = Gia_ManBalance( pWork, 0, 0, fVerbose );
            if ( !pNext ) { Gia_ManStop(pWork); return NULL; }
            Gia_ManStop( pWork );
            pWork = pNext;
        }
        pNext = Pass == 1 ? Drf_ManRefactorWithStop(pWork, 0, fVerbose, pFuncStop, pStopData)
                         : Drw_ManRewriteWithStop(pWork, 0, fVerbose, pFuncStop, pStopData);
        if ( !pNext ) { Gia_ManStop(pWork); return NULL; }
        Gia_ManStop( pWork );
        pWork = pNext;
    }
    // Compact rewriting may export duplicate ANDs. Solver conversion expects
    // structural hashing; normalize the final graph without balancing it.
    pNext = Gia_ManDupNormalize( pWork, 1 );
    Gia_ManStop( pWork );
    pWork = pNext;
    if ( pFuncStop && pFuncStop(pStopData) ) { Gia_ManStop(pWork); return NULL; }
    // All passes preserve the interface, including explicit initialization.
    pWork->nConstrs = pGia->nConstrs;
    if ( pGia->vRegInits && !pWork->vRegInits )
        pWork->vRegInits = Vec_IntDup( pGia->vRegInits );
    if ( pGia->vNamesIn && !pWork->vNamesIn ) pWork->vNamesIn = Vec_PtrDupStr( pGia->vNamesIn );
    if ( pGia->vNamesOut && !pWork->vNamesOut ) pWork->vNamesOut = Vec_PtrDupStr( pGia->vNamesOut );
    return pWork;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
