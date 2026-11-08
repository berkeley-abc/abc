/**CFile****************************************************************

  FileName    [cecKind.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Bounded k-induction on sequential AIGs.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 22, 2026.]

  Revision    [$Id: cecKind.c,v 1.00 2026/10/22 00:00:00 alanmi Exp $]

***********************************************************************/

#include <limits.h>
#include "aig/gia/gia.h"
#include "sat/bsat/satSolver.h"
#include "cec.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Sets the defaults for the shallow induction precheck.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManKindSetDefaultParams( Cec_ParKind_t * pPars )
{
    memset( pPars, 0, sizeof(Cec_ParKind_t) );
    pPars->nFramesMax = 4;
    pPars->nConfLimit = 2000;
    pPars->nTimeOutMs = 250;
    pPars->nAndMax   = 200000;
    pPars->iFrame    = -1;
}

/**Function*************************************************************

  Synopsis    [Checks the induction deadline and external stop callback.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec_KindCheckStop( abctime TimeToStop, Cec_ParKind_t * pPars )
{
    return (pPars->pFuncStop && pPars->pFuncStop(pPars->RunId)) || (TimeToStop && Abc_Clock() >= TimeToStop);
}

/**Function*************************************************************

  Synopsis    [Builds one base or induction query for all property outputs.]

  Description [The base asks for a bad output in the first K initialized
  frames.  The step asks for K good frames followed by a bad one, starting
  from an arbitrary state.  Inputs are independent in every frame.]

  SideEffects [None on the input design.]

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Cec_KindFrames( Gia_Man_t * p, int nFrames, int fBase, abctime TimeToStop, Cec_ParKind_t * pPars )
{
    Gia_Man_t * pNew = Gia_ManStart( Gia_ManObjNum(p) ), * pTemp;
    Gia_Obj_t * pObj;
    Vec_Int_t * vRegs = Vec_IntStart( Gia_ManRegNum(p) );
    int * pCopy = ABC_CALLOC( int, Gia_ManObjNum(p) );
    unsigned char * pNeeded = ABC_CALLOC( unsigned char, Gia_ManObjNum(p) );
    int f, i, Bad, Last = nFrames - fBase, Query = fBase ? 0 : 1;
    // The last frame only needs the property cone.  Its next-state logic
    // cannot affect this obligation and need not be built then discarded.
    Gia_ManForEachPo( p, pObj, i )
        pNeeded[Gia_ObjFaninId0p(p, pObj)] = 1;
    for ( i = Gia_ManObjNum(p) - 1; i > 0; i-- )
    {
        if ( !(i & 1023) && Cec_KindCheckStop(TimeToStop, pPars) ) goto stopped;
        pObj = Gia_ManObj( p, i );
        if ( !pNeeded[i] || !Gia_ObjIsAnd(pObj) ) continue;
        pNeeded[Gia_ObjFaninId0(pObj, i)] = 1;
        pNeeded[Gia_ObjFaninId1(pObj, i)] = 1;
    }
    Gia_ManHashStart( pNew );
    if ( !fBase )
        for ( i = 0; i < Gia_ManRegNum(p); i++ )
            Vec_IntWriteEntry( vRegs, i, Gia_ManAppendCi(pNew) );
    for ( f = 0; f < nFrames + !fBase; f++ )
    {
        if ( Cec_KindCheckStop(TimeToStop, pPars) ) goto stopped;
        Gia_ManForEachPi( p, pObj, i )
            pCopy[Gia_ObjId(p, pObj)] = Gia_ManAppendCi( pNew );
        Gia_ManForEachRo( p, pObj, i )
            pCopy[Gia_ObjId(p, pObj)] = Vec_IntEntry( vRegs, i );
        Gia_ManForEachAnd( p, pObj, i )
        {
            if ( !(i & 1023) && Cec_KindCheckStop(TimeToStop, pPars) ) goto stopped;
            if ( f == Last && !pNeeded[i] ) continue;
            pCopy[i] = Gia_ManHashAnd( pNew,
                pCopy[Gia_ObjFaninId0(pObj, i)] ^ Gia_ObjFaninC0(pObj),
                pCopy[Gia_ObjFaninId1(pObj, i)] ^ Gia_ObjFaninC1(pObj) );
        }
        Bad = 0;
        Gia_ManForEachPo( p, pObj, i )
            Bad = Gia_ManHashOr( pNew, Bad, pCopy[Gia_ObjFaninId0p(p, pObj)] ^ Gia_ObjFaninC0(pObj) );
        if ( fBase )
            Query = Gia_ManHashOr( pNew, Query, Bad );
        else
            Query = Gia_ManHashAnd( pNew, Query, f == nFrames ? Bad : Abc_LitNot(Bad) );
        if ( f < Last )
            Gia_ManForEachRi( p, pObj, i )
                Vec_IntWriteEntry( vRegs, i, pCopy[Gia_ObjFaninId0p(p, pObj)] ^ Gia_ObjFaninC0(pObj) );
    }
    Gia_ManAppendCo( pNew, Query );
    Gia_ManHashStop( pNew );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    ABC_FREE( pCopy );
    ABC_FREE( pNeeded );
    Vec_IntFree( vRegs );
    return pNew;
stopped:
    Gia_ManStop( pNew );
    ABC_FREE( pCopy );
    ABC_FREE( pNeeded );
    Vec_IntFree( vRegs );
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Discharges one bounded induction obligation.]

  Description [Returns 1 for UNSAT, 0 for SAT, and -1 for an interrupted or
  limited query. No SAT model is reported as an original counterexample.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec_KindQuery( Gia_Man_t * p, abctime TimeToStop, Cec_ParKind_t * pPars )
{
    Gia_Obj_t * pObj;
    sat_solver * pSat;
    int i, Lit = Gia_ObjFaninLit0p(p, Gia_ManPo(p, 0)), Result = -1;
    if ( Lit == 0 ) return 1;
    if ( Lit == 1 ) return 0;
    if ( Cec_KindCheckStop(TimeToStop, pPars) ) return -1;
    pSat = sat_solver_new();
    sat_solver_setnvars( pSat, Gia_ManObjNum(p) );
    sat_solver_set_stop_func( pSat, pPars->pFuncStop );
    sat_solver_set_runid( pSat, pPars->RunId );
    sat_solver_set_runtime_limit( pSat, TimeToStop );
    sat_solver_add_const( pSat, 0, 1 );
    Gia_ManForEachAnd( p, pObj, i )
    {
        if ( !(i & 1023) && Cec_KindCheckStop(TimeToStop, pPars) ) goto finish;
        sat_solver_add_and( pSat, i, Gia_ObjFaninId0(pObj, i), Gia_ObjFaninId1(pObj, i), Gia_ObjFaninC0(pObj), Gia_ObjFaninC1(pObj), 0 );
    }
    pPars->nQueries++;
    Result = sat_solver_solve( pSat, &Lit, &Lit + 1, pPars->nConfLimit, 0, 0, 0 );
    Result = Result == l_False ? 1 : Result == l_True ? 0 : -1;
finish:
    sat_solver_delete( pSat );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Proves safety with bounded k-induction.]

  Description [Returns 1 only when both base and step are UNSAT, and -1
  otherwise.  The base uses the all-zero initial state.  All property
  outputs are checked together; a SAT query is not a reported CEX.
  The input AIG and its annotations are not modified.  This API uses
  no global frame, thread-local storage, or worker threads.]

  SideEffects [Sets iFrame to the proved depth and counts SAT calls in nQueries.]

  SeeAlso     []

***********************************************************************/
int Cec_GiaKind( Gia_Man_t * p, Cec_ParKind_t * pPars )
{
    abctime TimeToStop;
    Gia_Man_t * pQuery;
    int k, Status, nFramesMax, i, Init;
    if ( pPars == NULL ) return -1;
    pPars->iFrame = -1;
    pPars->nQueries = 0;
    if ( p == NULL || pPars->nFramesMax < 1 || pPars->nFramesMax >= INT_MAX ||
         pPars->nConfLimit < 0 || pPars->nTimeOutMs < 0 || pPars->nAndMax < 0 )
        return -1;
    TimeToStop = pPars->nTimeOutMs > 0 ? Abc_Clock() + (abctime)pPars->nTimeOutMs * CLOCKS_PER_SEC / 1000 : 0;
    if ( pPars->TimeToStop && (!TimeToStop || pPars->TimeToStop < TimeToStop) )
        TimeToStop = pPars->TimeToStop;
    // Raw AIGER reads may retain explicit initialization. The base query
    // assumes zero; other initial values must be normalized by the caller.
    if ( p->vRegInits )
    {
        if ( Vec_IntSize(p->vRegInits) != Gia_ManRegNum(p) ) return -1;
        Vec_IntForEachEntry( p->vRegInits, Init, i )
            if ( Init != 0 )
            {
                if ( pPars->fVerbose ) Abc_Print( 1, "Kind requires normalized zero initial states (load AIGER with &read without -s).\n" );
                return -1;
            }
    }
    if ( Gia_ManConstrNum(p) || Gia_ManXorNum(p) || Gia_ManMuxNum(p) || Gia_ManBufNum(p) || Gia_ManBoxNum(p) )
    {
        if ( pPars->fVerbose ) Abc_Print( 1, "Kind requires a plain AIG without constraints or boxes.\n" );
        return -1;
    }
    if ( pPars->nAndMax && Gia_ManAndNum(p) > pPars->nAndMax )
    {
        if ( pPars->fVerbose ) Abc_Print( 1, "Kind skipped: %d ANDs exceed the limit of %d.\n", Gia_ManAndNum(p), pPars->nAndMax );
        return -1;
    }
    // Hashing the frames already exposes structural identities.  Avoid
    // sweeping the whole sequential design before these small queries.
    // A combinational miter has only the K = 0 obligation.
    nFramesMax = Gia_ManRegNum(p) ? pPars->nFramesMax : 0;
    for ( k = Gia_ManRegNum(p) > 0; k <= nFramesMax && !Cec_KindCheckStop(TimeToStop, pPars); k++ )
    {
        pQuery = Cec_KindFrames( p, k, 0, TimeToStop, pPars );
        if ( pQuery == NULL ) break;
        Status = Cec_KindQuery( pQuery, TimeToStop, pPars );
        if ( pPars->fVerbose ) Abc_Print( 1, "Kind K = %d: step %s (%d ANDs).\n", k, Status == 1 ? "UNSAT" : "not proved", Gia_ManAndNum(pQuery) );
        Gia_ManStop( pQuery );
        if ( Status != 1 ) continue;
        if ( k == 0 ) { pPars->iFrame = 0; return 1; } // combinational tautology
        pQuery = Cec_KindFrames( p, k, 1, TimeToStop, pPars );
        if ( pQuery == NULL ) break;
        Status = Cec_KindQuery( pQuery, TimeToStop, pPars );
        if ( pPars->fVerbose ) Abc_Print( 1, "Kind K = %d: base %s (%d ANDs).\n", k, Status == 1 ? "UNSAT" : "not proved", Gia_ManAndNum(pQuery) );
        Gia_ManStop( pQuery );
        if ( Status == 1 ) { pPars->iFrame = k; return 1; }
        // A longer initialized prefix still contains this satisfying trace.
        // A resource-limited query is inconclusive and can be retried at K+1.
        if ( Status == 0 ) break;
    }
    return -1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
