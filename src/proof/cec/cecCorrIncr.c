/**CFile****************************************************************

  FileName    [cecCorrIncr.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Incremental active-list / TFO filter for &scorr.]

  Author      [Xiran Zhao]

  Affiliation [University of Chinese Academy of Sciences]

  Date        [Ver. 1.0. Started - May 2026.]

***********************************************************************/

#include "cecInt.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates the incremental active-list manager.]

  Description [The manager owns one snapshot of pReprs/pNexts plus the
  TFO bookkeeping arrays.  pAig must outlive the manager; the manager
  never duplicates the AIG, only references it.  If the host AIG does
  not yet carry a static fanout, this routine builds it and remembers
  to tear it down on Free.]

  SideEffects [Builds static fanout on pAig if not already present.]

  SeeAlso     []

***********************************************************************/
Cec_IncrMgr_t * Cec_IncrMgrAlloc( Gia_Man_t * pAig, int nFrames )
{
    Cec_IncrMgr_t * p = ABC_CALLOC( Cec_IncrMgr_t, 1 );
    p->pAig      = pAig;
    p->nFrames   = nFrames;
    p->nObjs     = Gia_ManObjNum(pAig);
    p->vReprPrev = Vec_IntStartFull( p->nObjs );
    p->vNextPrev = Vec_IntStart( p->nObjs );
    p->vSeeds    = Vec_IntAlloc( 64 );
    p->vTfoNodes = Vec_IntAlloc( 1024 );
    p->pTfoMark  = ABC_CALLOC( int, p->nObjs );
    p->vAliasHeads = Vec_IntStartFull( p->nObjs );
    p->vAliasNext  = Vec_IntStartFull( p->nObjs );
    p->vBfsCur   = Vec_IntAlloc( 1024 );
    p->vBfsNext  = Vec_IntAlloc( 1024 );
    if ( pAig->vFanout == NULL )
    {
        Gia_ManStaticFanoutStart( pAig );
        p->fOwnsFanout = 1;
    }
    return p;
}

/**Function*************************************************************

  Synopsis    [Frees the incremental manager.]

  Description [Releases all internal vectors and the TFO mark array.
  If the manager built the static fanout on Alloc, it is also torn
  down here.  Safe to call with a NULL pointer.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_IncrMgrFree( Cec_IncrMgr_t * p )
{
    if ( p == NULL ) return;
    if ( p->fOwnsFanout )
        Gia_ManStaticFanoutStop( p->pAig );
    Vec_IntFree( p->vReprPrev );
    Vec_IntFree( p->vNextPrev );
    Vec_IntFree( p->vSeeds );
    Vec_IntFree( p->vTfoNodes );
    Vec_IntFree( p->vAliasHeads );
    Vec_IntFree( p->vAliasNext );
    Vec_IntFree( p->vBfsCur );
    Vec_IntFree( p->vBfsNext );
    ABC_FREE( p->pTfoMark );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Snapshots the current equivalence-class state.]

  Description [Copies the per-node pReprs and pNexts arrays into the
  manager so the next iteration can diff against the class state whose
  pairs were just emitted into the SRM.  Should be called after SRM
  construction and before SAT/sim refinement: the snapshot then reflects
  exactly the pairs the SAT solver was asked to prove.  O(N).]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_IncrMgrSnapshotClasses( Cec_IncrMgr_t * p )
{
    Gia_Man_t * pAig = p->pAig;
    int i;
    assert( pAig->pReprs != NULL );
    for ( i = 0; i < p->nObjs; i++ )
    {
        Vec_IntWriteEntry( p->vReprPrev, i, Gia_ObjRepr(pAig, i) );
        Vec_IntWriteEntry( p->vNextPrev, i, pAig->pNexts ? Gia_ObjNext(pAig, i) : 0 );
    }
}

/**Function*************************************************************

  Synopsis    [Computes the seed set for the next TFO BFS.]

  Description [Returns the number of nodes whose representative changed
  since the last snapshot and stores them in vSeeds.  Does not update
  the snapshot.

  pNexts changes are intentionally excluded here: a ring-link rewrite is
  an edge-local event that creates a new ring edge to reprove, not a new
  fanout cone, so it is handled by Cec_IncrMgrRingEdgeChanged at SRM
  emission time.]

  SideEffects []

  SeeAlso     [Cec_IncrMgrComputeTfo Cec_IncrMgrRingEdgeChanged]

***********************************************************************/
int Cec_IncrMgrComputeSeeds( Cec_IncrMgr_t * p )
{
    Gia_Man_t * pAig = p->pAig;
    int i, reprNew, reprOld;
    Vec_IntClear( p->vSeeds );
    for ( i = 1; i < p->nObjs; i++ )
    {
        reprNew = Gia_ObjRepr( pAig, i );
        reprOld = Vec_IntEntry( p->vReprPrev, i );
        if ( reprNew != reprOld )
            Vec_IntPush( p->vSeeds, i );
    }
    return Vec_IntSize( p->vSeeds );
}

/**Function*************************************************************

  Synopsis    [Counts nodes whose ring-list successor changed.]

  Description [Used only for convergence and fallback decisions.  These
  nodes are NOT TFO seeds, because a pNexts-only change creates a new
  ring edge (proved edge-locally by the active SRM builder) rather than
  a new fanout cone to re-prove.  Returns 0 when pNexts is unallocated,
  i.e. when ring mode is off.]

  SideEffects []

  SeeAlso     [Cec_IncrMgrComputeSeeds]

***********************************************************************/
int Cec_IncrMgrCountNextChanges( Cec_IncrMgr_t * p )
{
    Gia_Man_t * pAig = p->pAig;
    int i, nChanges = 0;
    if ( pAig->pNexts == NULL )
        return 0;
    for ( i = 1; i < p->nObjs; i++ )
        nChanges += Gia_ObjNext( pAig, i ) != Vec_IntEntry( p->vNextPrev, i );
    return nChanges;
}

/**Function*************************************************************

  Synopsis    [Detects whether a ring edge is new since the last snapshot.]

  Description [Ring classes store list edges explicitly in pNexts, but
  the SRM also proves the implicit closing edge tail -> head.  For an
  explicit edge, the edge is unchanged iff the predecessor's pNexts slot
  still names the same successor.  For the closing edge there is no
  pNexts slot to compare, so we reconstruct whether the same tail/head
  pair already existed in the previous snapshot: the tail must have been
  pointing to the head (closing the ring) and the head must still have
  been a class root.  Returns 1 to mean "must be re-proved".  Passing a
  NULL manager or a non-ring AIG returns 0 (no edge work needed).]

  SideEffects []

  SeeAlso     [Cec_IncrMgrCountActivePairs]

***********************************************************************/
int Cec_IncrMgrRingEdgeChanged( Cec_IncrMgr_t * p, int iPrev, int iObj )
{
    Gia_Man_t * pAig;
    int iNextCur, iNextOld;
    if ( p == NULL )
        return 0;
    pAig = p->pAig;
    if ( pAig->pNexts == NULL )
        return 0;
    iNextCur = Gia_ObjNext( pAig, iPrev );
    iNextOld = Vec_IntEntry( p->vNextPrev, iPrev );
    if ( iNextCur == iObj )
        return iNextOld != iObj;
    if ( iNextCur > 0 )
        return 1; // conservative: should not happen for callers below
    // Closing edge: prove if the previous snapshot did not already contain
    // exactly this tail/head pair as a ring's closing edge.
    return iNextOld > 0 ||
           Vec_IntEntry( p->vReprPrev, iPrev ) != iObj ||
           Vec_IntEntry( p->vReprPrev, iObj ) != GIA_VOID ||
           Vec_IntEntry( p->vNextPrev, iObj ) <= 0;
}

/**Function*************************************************************

  Synopsis    [Counts total and active candidate pairs before SRM build.]

  Description [Mirrors the PO-emission loops in the active SRM builders
  but stops before constructing the unrolled network: it walks every
  candidate pair the SRM would emit and tallies how many would survive
  the active filter (pTfoMark plus the ring-edge override).  The count
  is approximate because SRM construction can still simplify a pair
  away after the literal it represents collapses; it is used only to
  decide whether the active filter saves enough work to be worth the
  bookkeeping (the main loop falls back to the full SRM above ~70%
  active pairs).  When pTfoMark is NULL every pair is counted active.]

  SideEffects []

  SeeAlso     [Gia_ManCorrSpecReduce_Emit]

***********************************************************************/
void Cec_IncrMgrCountActivePairs( Cec_IncrMgr_t * p, int fRings, int * pTfoMark,
                                  int * pnTotal, int * pnActive )
{
    Gia_Man_t * pAig = p->pAig;
    Gia_Obj_t * pObj, * pRepr;
    int i, iPrev, iObj;
    *pnTotal = *pnActive = 0;
    assert( pAig->pReprs != NULL );
    if ( fRings )
    {
        Gia_ManForEachObj1( pAig, pObj, i )
        {
            if ( Gia_ObjIsConst( pAig, i ) )
            {
                (*pnTotal)++;
                (*pnActive) += pTfoMark == NULL || pTfoMark[i];
            }
            else if ( Gia_ObjIsHead( pAig, i ) )
            {
                iPrev = i;
                Gia_ClassForEachObj1( pAig, i, iObj )
                {
                    (*pnTotal)++;
                    (*pnActive) += pTfoMark == NULL || pTfoMark[iPrev] || pTfoMark[iObj] ||
                                   Cec_IncrMgrRingEdgeChanged( p, iPrev, iObj );
                    iPrev = iObj;
                }
                iObj = i; // closing edge tail -> head
                (*pnTotal)++;
                (*pnActive) += pTfoMark == NULL || pTfoMark[iPrev] || pTfoMark[iObj] ||
                               Cec_IncrMgrRingEdgeChanged( p, iPrev, iObj );
            }
        }
    }
    else
    {
        Gia_ManForEachObj1( pAig, pObj, i )
        {
            int idR;
            pRepr = Gia_ObjReprObj( pAig, Gia_ObjId(pAig,pObj) );
            if ( pRepr == NULL )
                continue;
            idR = Gia_ObjId( pAig, pRepr );
            (*pnTotal)++;
            (*pnActive) += pTfoMark == NULL || pTfoMark[i] || pTfoMark[idR];
        }
    }
}

/**Function*************************************************************

  Synopsis    [Forward TFO BFS from seeds across nFrames unrollings.]

  Description [Marks pTfoMark[id]=1 for every SRM node reachable from
  any seed within nFrames combinational+sequential steps.  Besides AIG
  fanouts, the walk follows representative-to-member alias edges because
  Gia_ManCorrSpecReduce_rec(member) uses repr(member) directly.  Missing
  these edges can reuse an obsolete UNSAT result when a representative's
  reduced value changes through another member's fanout cone.

  Each frame performs a combinational fanout BFS; RI fanouts cross to the
  next frame by following Gia_ObjRiToRo to the corresponding register
  output.  After nFrames cross-frame jumps the search stops, since pairs
  deeper than that cannot depend on the seeds within an nFrames-deep SRM.

  RI nodes themselves are intentionally not marked: SRM emission is
  keyed on AIG candidate nodes (ANDs and CIs) and never on COs, so
  marking RIs would only inflate the active set without enabling any
  additional pair.

  Mark clearing is amortised: vTfoNodes records every id touched in
  the previous round and is iterated to zero only those entries, so
  the routine never sweeps the full N-sized array.  Cost per call is
  O(|TFO_k| * avg_fanout).]

  SideEffects []

  SeeAlso     [Cec_IncrMgrComputeSeeds]

***********************************************************************/
void Cec_IncrMgrComputeTfo( Cec_IncrMgr_t * p )
{
    Gia_Man_t * pAig = p->pAig;
    int * pMark = p->pTfoMark;
    int f, i, k, Id, FanId, RoId, ReprId, AliasId;

    Vec_IntForEachEntry( p->vTfoNodes, Id, i )
        pMark[Id] = 0;
    Vec_IntClear( p->vTfoNodes );
    Vec_IntClear( p->vBfsCur );
    Vec_IntClear( p->vBfsNext );

    Vec_IntFill( p->vAliasHeads, p->nObjs, -1 );
    Vec_IntFill( p->vAliasNext,  p->nObjs, -1 );
    for ( Id = 1; Id < p->nObjs; Id++ )
    {
        ReprId = Gia_ObjRepr( pAig, Id );
        if ( ReprId <= 0 || ReprId == GIA_VOID )
            continue;
        Vec_IntWriteEntry( p->vAliasNext, Id, Vec_IntEntry(p->vAliasHeads, ReprId) );
        Vec_IntWriteEntry( p->vAliasHeads, ReprId, Id );
    }

    Vec_IntForEachEntry( p->vSeeds, Id, i )
    {
        if ( !pMark[Id] )
        {
            pMark[Id] = 1;
            Vec_IntPush( p->vTfoNodes, Id );
            Vec_IntPush( p->vBfsCur, Id );
        }
    }

    for ( f = 0; f <= p->nFrames; f++ )
    {
        int head = 0;
        while ( head < Vec_IntSize(p->vBfsCur) )
        {
            Gia_Obj_t * pFan;
            Id = Vec_IntEntry( p->vBfsCur, head++ );
            for ( AliasId = Vec_IntEntry(p->vAliasHeads, Id);
                  AliasId >= 0;
                  AliasId = Vec_IntEntry(p->vAliasNext, AliasId) )
            {
                if ( pMark[AliasId] )
                    continue;
                pMark[AliasId] = 1;
                Vec_IntPush( p->vTfoNodes, AliasId );
                Vec_IntPush( p->vBfsCur, AliasId );
            }
            int nFan = Gia_ObjFanoutNumId( pAig, Id );
            for ( k = 0; k < nFan; k++ )
            {
                FanId = Gia_ObjFanoutId( pAig, Id, k );
                pFan  = Gia_ManObj( pAig, FanId );
                if ( Gia_ObjIsRi(pAig, pFan) )
                {
                    if ( f < p->nFrames )
                    {
                        RoId = Gia_ObjRiToRoId( pAig, FanId );
                        if ( !pMark[RoId] )
                        {
                            pMark[RoId] = 1;
                            Vec_IntPush( p->vTfoNodes, RoId );
                            Vec_IntPush( p->vBfsNext, RoId );
                        }
                    }
                }
                else if ( Gia_ObjIsCo(pFan) )
                {
                    // PO: not a candidate, skip
                }
                else
                {
                    if ( !pMark[FanId] )
                    {
                        pMark[FanId] = 1;
                        Vec_IntPush( p->vTfoNodes, FanId );
                        Vec_IntPush( p->vBfsCur, FanId );
                    }
                }
            }
        }
        Vec_IntClear( p->vBfsCur );
        Vec_IntAppend( p->vBfsCur, p->vBfsNext );
        Vec_IntClear( p->vBfsNext );
        if ( Vec_IntSize(p->vBfsCur) == 0 )
            break;
    }
}

/**Function*************************************************************

  Synopsis    [Emission-filtered variant of Gia_ManCorrSpecReduce.]

  Description [Identical to Gia_ManCorrSpecReduce in its SRM topology
  and speculative reduction; the only difference is PO emission.
  CEC_EMIT_ACTIVE emits pairs selected by the incremental TFO filter.
  CEC_EMIT_SKIPPED emits the exact complement for shadow validation.
  A new or rewired ring edge is always active and can never be emitted
  as skipped because it has no prior UNSAT result to reuse.

  Walking the full ring is required (rather than skipping unmarked
  members) so iPrev stays aligned with the live class order; the active
  predicate is evaluated only after the edge endpoints are known.]

  SideEffects []

  SeeAlso     [Gia_ManCorrSpecReduce Cec_IncrMgrCountActivePairs]

***********************************************************************/
Gia_Man_t * Gia_ManCorrSpecReduce_Emit( Gia_Man_t * p, int nFrames, int fScorr,
                                        Vec_Int_t ** pvOutputs, int fRings,
                                        int * pTfoMark, Cec_IncrMgr_t * pIncr,
                                        Cec_IncrEmitMode_t Mode, Vec_Int_t ** pvOutLits )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj, * pRepr;
    Vec_Int_t * vXorLits;
    int f, i, iPrev, iObj, iPrevNew, iObjNew, iPrevRaw, iObjRaw;
    assert( nFrames > 0 );
    assert( Gia_ManRegNum(p) > 0 );
    assert( p->pReprs != NULL );
    assert( Mode == CEC_EMIT_ALL || pTfoMark != NULL );
    Vec_IntFill( &p->vCopies, (nFrames+fScorr)*Gia_ManObjNum(p), -1 );
    Gia_ManSetPhase( p );
    pNew = Gia_ManStart( nFrames * Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManHashAlloc( pNew );
    Gia_ObjSetCopyF( p, 0, Gia_ManConst0(p), 0 );
    Gia_ManForEachRo( p, pObj, i )
        Gia_ObjSetCopyF( p, 0, pObj, Gia_ManAppendCi(pNew) );
    Gia_ManForEachRo( p, pObj, i )
        if ( (pRepr = Gia_ObjReprObj(p, Gia_ObjId(p, pObj))) )
            Gia_ObjSetCopyF( p, 0, pObj, Gia_ObjCopyF(p, 0, pRepr) );
    for ( f = 0; f < nFrames+fScorr; f++ )
    {
        Gia_ObjSetCopyF( p, f, Gia_ManConst0(p), 0 );
        Gia_ManForEachPi( p, pObj, i )
            Gia_ObjSetCopyF( p, f, pObj, Gia_ManAppendCi(pNew) );
    }
    *pvOutputs = Vec_IntAlloc( 1000 );
    if ( pvOutLits )
        *pvOutLits = Vec_IntAlloc( 1000 );
    vXorLits = Vec_IntAlloc( 1000 );
    if ( fRings )
    {
        Gia_ManForEachObj1( p, pObj, i )
        {
            if ( Gia_ObjIsConst( p, i ) )
            {
                int fActive = pTfoMark != NULL && pTfoMark[i];
                int fEmit = Mode == CEC_EMIT_ALL ||
                            (Mode == CEC_EMIT_ACTIVE  &&  fActive) ||
                            (Mode == CEC_EMIT_SKIPPED && !fActive);
                if ( !fEmit )
                    continue;
                iObjRaw = Gia_ManCorrSpecReal( pNew, p, pObj, nFrames, 0 );
                iObjNew = Abc_LitNotCond( iObjRaw, Gia_ObjPhase(pObj) );
                if ( iObjNew != 0 )
                {
                    Vec_IntPush( *pvOutputs, 0 );
                    Vec_IntPush( *pvOutputs, i );
                    if ( pvOutLits )
                    {
                        Vec_IntPush( *pvOutLits, 0 );
                        Vec_IntPush( *pvOutLits, iObjRaw );
                    }
                    Vec_IntPush( vXorLits, iObjNew );
                }
            }
            else if ( Gia_ObjIsHead( p, i ) )
            {
                // Walk every ring edge so iPrev stays aligned with the class
                // order; emit only when an endpoint is in TFO or the edge is
                // new/rewired since the last snapshot.
                iPrev = i;
                Gia_ClassForEachObj1( p, i, iObj )
                {
                    int fActive = pTfoMark != NULL &&
                                  (pTfoMark[iPrev] || pTfoMark[iObj] ||
                                   Cec_IncrMgrRingEdgeChanged( pIncr, iPrev, iObj ));
                    int fEmit = Mode == CEC_EMIT_ALL ||
                                (Mode == CEC_EMIT_ACTIVE  &&  fActive) ||
                                (Mode == CEC_EMIT_SKIPPED && !fActive);
                    if ( fEmit )
                    {
                        iPrevRaw = Gia_ManCorrSpecReal( pNew, p, Gia_ManObj(p, iPrev), nFrames, 0 );
                        iObjRaw  = Gia_ManCorrSpecReal( pNew, p, Gia_ManObj(p, iObj), nFrames, 0 );
                        iPrevNew = Abc_LitNotCond( iPrevRaw, Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p, iPrev)) );
                        iObjNew  = Abc_LitNotCond( iObjRaw,  Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p, iObj)) );
                        if ( iPrevNew != iObjNew && iPrevNew != 0 && iObjNew != 1 )
                        {
                            Vec_IntPush( *pvOutputs, iPrev );
                            Vec_IntPush( *pvOutputs, iObj );
                            if ( pvOutLits )
                            {
                                Vec_IntPush( *pvOutLits, iPrevRaw );
                                Vec_IntPush( *pvOutLits, iObjRaw );
                            }
                            Vec_IntPush( vXorLits, Gia_ManHashAnd(pNew, iPrevNew, Abc_LitNot(iObjNew)) );
                        }
                    }
                    iPrev = iObj;
                }
                // Closing edge tail -> head
                iObj = i;
                {
                    int fActive = pTfoMark != NULL &&
                                  (pTfoMark[iPrev] || pTfoMark[iObj] ||
                                   Cec_IncrMgrRingEdgeChanged( pIncr, iPrev, iObj ));
                    int fEmit = Mode == CEC_EMIT_ALL ||
                                (Mode == CEC_EMIT_ACTIVE  &&  fActive) ||
                                (Mode == CEC_EMIT_SKIPPED && !fActive);
                    if ( fEmit )
                    {
                        iPrevRaw = Gia_ManCorrSpecReal( pNew, p, Gia_ManObj(p, iPrev), nFrames, 0 );
                        iObjRaw  = Gia_ManCorrSpecReal( pNew, p, Gia_ManObj(p, iObj), nFrames, 0 );
                        iPrevNew = Abc_LitNotCond( iPrevRaw, Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p, iPrev)) );
                        iObjNew  = Abc_LitNotCond( iObjRaw,  Gia_ObjPhase(pObj) ^ Gia_ObjPhase(Gia_ManObj(p, iObj)) );
                        if ( iPrevNew != iObjNew && iPrevNew != 0 && iObjNew != 1 )
                        {
                            Vec_IntPush( *pvOutputs, iPrev );
                            Vec_IntPush( *pvOutputs, iObj );
                            if ( pvOutLits )
                            {
                                Vec_IntPush( *pvOutLits, iPrevRaw );
                                Vec_IntPush( *pvOutLits, iObjRaw );
                            }
                            Vec_IntPush( vXorLits, Gia_ManHashAnd(pNew, iPrevNew, Abc_LitNot(iObjNew)) );
                        }
                    }
                }
            }
        }
    }
    else
    {
        Gia_ManForEachObj1( p, pObj, i )
        {
            pRepr = Gia_ObjReprObj( p, Gia_ObjId(p,pObj) );
            if ( pRepr == NULL )
                continue;
            {
                int idR = Gia_ObjId(p, pRepr);
                int fActive = pTfoMark != NULL && (pTfoMark[i] || pTfoMark[idR]);
                int fEmit = Mode == CEC_EMIT_ALL ||
                            (Mode == CEC_EMIT_ACTIVE  &&  fActive) ||
                            (Mode == CEC_EMIT_SKIPPED && !fActive);
                if ( !fEmit )
                    continue;
            }
            iPrevRaw = Gia_ObjIsConst(p, i)? 0 : Gia_ManCorrSpecReal( pNew, p, pRepr, nFrames, 0 );
            iObjRaw  = Gia_ManCorrSpecReal( pNew, p, pObj, nFrames, 0 );
            iPrevNew = iPrevRaw;
            iObjNew  = Abc_LitNotCond( iObjRaw, Gia_ObjPhase(pRepr) ^ Gia_ObjPhase(pObj) );
            if ( iPrevNew != iObjNew )
            {
                Vec_IntPush( *pvOutputs, Gia_ObjId(p, pRepr) );
                Vec_IntPush( *pvOutputs, Gia_ObjId(p, pObj) );
                if ( pvOutLits )
                {
                    Vec_IntPush( *pvOutLits, iPrevRaw );
                    Vec_IntPush( *pvOutLits, iObjRaw );
                }
                Vec_IntPush( vXorLits, Gia_ManHashXor(pNew, iPrevNew, iObjNew) );
            }
        }
    }
    Vec_IntForEachEntry( vXorLits, iObjNew, i )
        Gia_ManAppendCo( pNew, iObjNew );
    Vec_IntFree( vXorLits );
    Gia_ManHashStop( pNew );
    Vec_IntErase( &p->vCopies );
    pNew = Gia_ManCleanup( pTemp = pNew );
    if ( pvOutLits )
        Gia_ManDupRemapLiterals( *pvOutLits, pTemp );
    Gia_ManStop( pTemp );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Active-filter variant of Gia_ManCorrSpecReduceInit (BMC SRM).]

  Description [Mirrors Gia_ManCorrSpecReduceInit but emits a candidate
  PO (pRepr, pObj) only when at least one of the two endpoints lies in
  pTfoMark.  The baseline BMC SRM accepts an fRings flag for symmetry
  with the inductive builder but never inspects it -- its topology is
  always (head, member) pairs derived from pReprs alone, with no ring
  edges to close.  Therefore this active variant only needs pReprs-
  driven seeds: pNexts changes cannot affect this SRM and there is no
  closing edge to reprove.  Passing pTfoMark == NULL falls back to the
  unfiltered baseline behaviour.]

  SideEffects []

  SeeAlso     [Gia_ManCorrSpecReduceInit]

***********************************************************************/
Gia_Man_t * Gia_ManCorrSpecReduceInit_Active( Gia_Man_t * p, int nFrames, int nPrefix, int fScorr,
                                              Vec_Int_t ** pvOutputs, int * pTfoMark )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj, * pRepr;
    Vec_Int_t * vXorLits;
    int f, i, iPrevNew, iObjNew;
    assert( (!fScorr && nFrames > 1) || (fScorr && nFrames > 0) || nPrefix );
    assert( Gia_ManRegNum(p) > 0 );
    assert( p->pReprs != NULL );
    Vec_IntFill( &p->vCopies, (nFrames+nPrefix+fScorr)*Gia_ManObjNum(p), -1 );
    Gia_ManSetPhase( p );
    pNew = Gia_ManStart( (nFrames+nPrefix) * Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManHashAlloc( pNew );
    Gia_ManForEachRo( p, pObj, i )
    {
        Gia_ManAppendCi(pNew);
        Gia_ObjSetCopyF( p, 0, pObj, 0 );
    }
    for ( f = 0; f < nFrames+nPrefix+fScorr; f++ )
    {
        Gia_ObjSetCopyF( p, f, Gia_ManConst0(p), 0 );
        Gia_ManForEachPi( p, pObj, i )
            Gia_ObjSetCopyF( p, f, pObj, Gia_ManAppendCi(pNew) );
    }
    *pvOutputs = Vec_IntAlloc( 1000 );
    vXorLits = Vec_IntAlloc( 1000 );
    for ( f = nPrefix; f < nFrames+nPrefix; f++ )
    {
        Gia_ManForEachObj1( p, pObj, i )
        {
            pRepr = Gia_ObjReprObj( p, Gia_ObjId(p,pObj) );
            if ( pRepr == NULL )
                continue;
            if ( pTfoMark )
            {
                int idR = Gia_ObjId(p, pRepr);
                if ( !pTfoMark[i] && !pTfoMark[idR] )
                    continue;
            }
            iPrevNew = Gia_ObjIsConst(p, i)? 0 : Gia_ManCorrSpecReal( pNew, p, pRepr, f, nPrefix );
            iObjNew  = Gia_ManCorrSpecReal( pNew, p, pObj, f, nPrefix );
            iObjNew  = Abc_LitNotCond( iObjNew, Gia_ObjPhase(pRepr) ^ Gia_ObjPhase(pObj) );
            if ( iPrevNew != iObjNew )
            {
                Vec_IntPush( *pvOutputs, Gia_ObjId(p, pRepr) );
                Vec_IntPush( *pvOutputs, Gia_ObjId(p, pObj) );
                Vec_IntPush( vXorLits, Gia_ManHashXor(pNew, iPrevNew, iObjNew) );
            }
        }
    }
    Vec_IntForEachEntry( vXorLits, iObjNew, i )
        Gia_ManAppendCo( pNew, iObjNew );
    Vec_IntFree( vXorLits );
    Gia_ManHashStop( pNew );
    Vec_IntErase( &p->vCopies );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
