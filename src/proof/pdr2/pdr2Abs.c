/**CFile****************************************************************

  FileName    [pdr2Abs.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Property directed reachability, second implementation.]

  Synopsis    [Localization abstraction of flops (PDRA).]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: pdr2Abs.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "pdr2Int.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// ternary values
#define PDR2_V0   0
#define PDR2_V1   1
#define PDR2_VX   2

// justification priorities (lower is preferred)
#define PDR2_PRIO_PPI_FREE  10000

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Projects a cube onto the abstraction.]

  Description [Keeps the literals of flops in the abstraction; the dropped
  literals (pseudo-input values) are collected in vPpis if given.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr2_ManAbsProject( Pdr2_Man_t * p, Vec_Int_t * vCube, Vec_Int_t * vPpis )
{
    int i, k = 0, Lit, fNonInit = 0, iBest = -1;
    if ( !p->fAbsActive )
        return;
    if ( vPpis )
        Vec_IntClear( vPpis );
    // if the kept literals all agree with the initial state while a dropped one does not,
    // keep the dropped one with the highest activity: the projected cube must not look initial
    Vec_IntForEachEntry( vCube, Lit, i )
        if ( p->pAbs[Abc_Lit2Var(Lit)] )
            fNonInit |= Pdr2_ManLitIsNonInit( p, Lit );
        else if ( Pdr2_ManLitIsNonInit(p, Lit) && (iBest == -1 || p->pAct[Abc_Lit2Var(Lit)] > p->pAct[Abc_Lit2Var(Vec_IntEntry(vCube, iBest))]) )
            iBest = i;
    if ( !fNonInit && iBest != -1 )
    {
        p->pAbs[Abc_Lit2Var(Vec_IntEntry(vCube, iBest))] = 1;
        p->nAbsFlops++;
        p->nAbsFixups++;
    }
    Vec_IntForEachEntry( vCube, Lit, i )
    {
        if ( p->pAbs[Abc_Lit2Var(Lit)] )
            Vec_IntWriteEntry( vCube, k++, Lit );
        else if ( vPpis )
            Vec_IntPush( vPpis, Lit );
    }
    Vec_IntShrink( vCube, k );
}

/**Function*************************************************************

  Synopsis    [Removes from the abstraction the flops absent from all lemmas.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr2_ManAbsCleanup( Pdr2_Man_t * p )
{
    Pdr2_Lem_t * pLem;
    int k, i, j, nRemoved = 0;
    if ( !p->fAbsActive || !p->pPars->fAbsCleanup )
        return;
    memset( p->pAbsUsed, 0, sizeof(char) * p->nRegs );
    for ( k = 1; k < Pdr2_ManFrameNum(p); k++ )
        Vec_PtrForEachEntry( Pdr2_Lem_t *, Pdr2_ManFrame(p, k), pLem, i )
            for ( j = 0; j < pLem->pCube->nLits; j++ )
                p->pAbsUsed[Abc_Lit2Var(pLem->pCube->Lits[j])] = 1;
    Vec_PtrForEachEntry( Pdr2_Lem_t *, p->vInf, pLem, i )
        for ( j = 0; j < pLem->pCube->nLits; j++ )
            p->pAbsUsed[Abc_Lit2Var(pLem->pCube->Lits[j])] = 1;
    for ( i = 0; i < p->nRegs; i++ )
        if ( p->pAbs[i] && !p->pAbsUsed[i] && i != p->iResetFlop )
        {
            p->pAbs[i] = 0;
            p->nAbsFlops--;
            nRemoved++;
        }
    p->nAbsCleaned += nRemoved;
}

/**Function*************************************************************

  Synopsis    [Gates the flop outputs with a reset flop.]

  Description [Adds a register that is 0 in the first cycle and 1 after
  it, and replaces the output of every flop with a defined initial value
  by its AND (initial value 0) or OR (initial value 1, with the negated
  register) with this register. In the first cycle the logic sees the
  initial values whatever the flops hold, so the flops themselves become
  unconstrained initially and only the reset register distinguishes the
  initial state. This is the encoding used by treb -abs: a cube can
  intersect the initial states only through the reset literal, so
  projected cubes do not look initial. The flops with a don't-care initial
  value are not gated. The new register is the last one. Returns the new
  design and, in ppInitNew, its initial values: don't-care for the
  ungated flops and 0 for all others. Traces (inputs, outputs) are
  unchanged.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Pdr2_ManDupGatedInit( Aig_Man_t * pAig, char * pInit, char ** ppInitNew )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj, * pReset;
    char * pInitNew = ABC_CALLOC( char, Aig_ManRegNum(pAig) + 2 );
    int i;
    pNew = Aig_ManStart( Aig_ManObjNumMax(pAig) + Aig_ManRegNum(pAig) + 2 );
    pNew->pName = Abc_UtilStrsav( pAig->pName );
    pNew->nConstrs = 0;
    Aig_ManConst1(pAig)->pData = Aig_ManConst1( pNew );
    Saig_ManForEachPi( pAig, pObj, i )
        pObj->pData = Aig_ObjCreateCi( pNew );
    Saig_ManForEachLo( pAig, pObj, i )
        pObj->pData = Aig_ObjCreateCi( pNew );
    pReset = Aig_ObjCreateCi( pNew );
    Saig_ManForEachLo( pAig, pObj, i )
        if ( pInit && pInit[i] == 2 )
            pInitNew[i] = 2;
        else if ( pInit && pInit[i] == 1 )
            pObj->pData = Aig_Not( Aig_And( pNew, Aig_Not((Aig_Obj_t *)pObj->pData), pReset ) );
        else
            pObj->pData = Aig_And( pNew, (Aig_Obj_t *)pObj->pData, pReset );
    Aig_ManForEachNode( pAig, pObj, i )
        pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
    Saig_ManForEachPo( pAig, pObj, i )
        Aig_ObjCreateCo( pNew, Aig_ObjChild0Copy(pObj) );
    Saig_ManForEachLi( pAig, pObj, i )
        Aig_ObjCreateCo( pNew, Aig_ObjChild0Copy(pObj) );
    Aig_ObjCreateCo( pNew, Aig_ManConst1(pNew) );
    Aig_ManSetRegNum( pNew, Aig_ManRegNum(pAig) + 1 );
    Aig_ManCleanup( pNew );
    *ppInitNew = pInitNew;
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Starts the abstraction with the flops used in the lemmas.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr2_ManAbsStart( Pdr2_Man_t * p )
{
    Pdr2_Lem_t * pLem;
    int k, i, j;
    p->fAbsActive = 1;
    if ( p->iResetFlop >= 0 && !p->pAbs[p->iResetFlop] )
    {
        p->pAbs[p->iResetFlop] = 1;
        p->nAbsFlops++;
    }
    for ( k = 1; k < Pdr2_ManFrameNum(p); k++ )
        Vec_PtrForEachEntry( Pdr2_Lem_t *, Pdr2_ManFrame(p, k), pLem, i )
            for ( j = 0; j < pLem->pCube->nLits; j++ )
                if ( !p->pAbs[Abc_Lit2Var(pLem->pCube->Lits[j])] )
                {
                    p->pAbs[Abc_Lit2Var(pLem->pCube->Lits[j])] = 1;
                    p->nAbsFlops++;
                }
    Vec_PtrForEachEntry( Pdr2_Lem_t *, p->vInf, pLem, i )
        for ( j = 0; j < pLem->pCube->nLits; j++ )
            if ( !p->pAbs[Abc_Lit2Var(pLem->pCube->Lits[j])] )
            {
                p->pAbs[Abc_Lit2Var(pLem->pCube->Lits[j])] = 1;
                p->nAbsFlops++;
            }
    if ( p->pPars->fVerbose )
        Abc_Print( 1, "Starting the abstraction at level %d with %d of %d flops.\n", Pdr2_ManLevel(p), p->nAbsFlops, p->nRegs );
}

/**Function*************************************************************

  Synopsis    [Ternary simulation of one frame.]

  Description [pVals holds the values of all objects of this frame; the
  CI values must be set before the call. Internal nodes and COs are computed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Pdr2_ValNot( int v, int fCompl )
{
    return v == PDR2_VX ? PDR2_VX : (v ^ fCompl);
}
static void Pdr2_ManAbsSimFrame( Pdr2_Man_t * p, char * pVals )
{
    Aig_Obj_t * pObj;
    int i, v0, v1;
    pVals[Aig_ObjId(Aig_ManConst1(p->pAig))] = PDR2_V1;
    Aig_ManForEachNode( p->pAig, pObj, i )
    {
        v0 = Pdr2_ValNot( pVals[Aig_ObjFaninId0(pObj)], Aig_ObjFaninC0(pObj) );
        v1 = Pdr2_ValNot( pVals[Aig_ObjFaninId1(pObj)], Aig_ObjFaninC1(pObj) );
        if ( v0 == PDR2_V0 || v1 == PDR2_V0 )
            pVals[i] = PDR2_V0;
        else if ( v0 == PDR2_V1 && v1 == PDR2_V1 )
            pVals[i] = PDR2_V1;
        else
            pVals[i] = PDR2_VX;
    }
    Aig_ManForEachCo( p->pAig, pObj, i )
        pVals[Aig_ObjId(pObj)] = Pdr2_ValNot( pVals[Aig_ObjFaninId0(pObj)], Aig_ObjFaninC0(pObj) );
}

/**Function*************************************************************

  Synopsis    [Ternary propagation of one changed value within one frame.]

  Description [Sets the object to the value and propagates through the
  fanouts. Changed positions are recorded in vUndo (position, old value).
  Returns 0 as soon as a marked target output changes.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pdr2_ManSimXProp1( Pdr2_Man_t * p, char * pVals, char * pMark, Vec_Int_t * vUndo, Vec_Int_t * vWork, int Id, int Val )
{
    Aig_Man_t * pAig = p->pAig;
    Aig_Obj_t * pObj, * pFan;
    int * pTrav = p->pLiftTrav, nTrav = p->nLiftTrav;
    int iFan, k, Old, New, FanId, v0, v1;
    if ( pVals[Id] == Val )
        return 1;
    Vec_IntClear( vWork );
    Vec_IntPushTwo( vUndo, Id, pVals[Id] );
    pVals[Id] = (char)Val;
    Vec_IntPush( vWork, Id );
    while ( Vec_IntSize(vWork) > 0 )
    {
        Id = Vec_IntPop( vWork );
        pObj = Aig_ManObj( pAig, Id );
        Aig_ObjForEachFanout( pAig, pObj, pFan, iFan, k )
        {
            FanId = Aig_ObjId( pFan );
            if ( pTrav[FanId] != nTrav )
                continue;  // outside the cone of the targets
            Old = pVals[FanId];
            if ( Aig_ObjIsNode(pFan) )
            {
                v0 = Pdr2_ValNot( pVals[Aig_ObjFaninId0(pFan)], Aig_ObjFaninC0(pFan) );
                v1 = Pdr2_ValNot( pVals[Aig_ObjFaninId1(pFan)], Aig_ObjFaninC1(pFan) );
                New = (v0 == PDR2_V0 || v1 == PDR2_V0) ? PDR2_V0 : (v0 == PDR2_V1 && v1 == PDR2_V1) ? PDR2_V1 : PDR2_VX;
                if ( New == Old )
                    continue;
                Vec_IntPushTwo( vUndo, FanId, Old );
                pVals[FanId] = (char)New;
                Vec_IntPush( vWork, FanId );
                continue;
            }
            assert( Aig_ObjIsCo(pFan) );
            New = Pdr2_ValNot( pVals[Aig_ObjFaninId0(pFan)], Aig_ObjFaninC0(pFan) );
            if ( New == Old )
                continue;
            Vec_IntPushTwo( vUndo, FanId, Old );
            pVals[FanId] = (char)New;
            if ( pMark[FanId] == 1 )
                return 0;
        }
    }
    return 1;
}
static void Pdr2_ManSimXUndo1( char * pVals, Vec_Int_t * vUndo )
{
    int i;
    for ( i = Vec_IntSize(vUndo) - 2; i >= 0; i -= 2 )
        pVals[Vec_IntEntry(vUndo, i)] = (char)Vec_IntEntry( vUndo, i + 1 );
    Vec_IntClear( vUndo );
}

// collects the cone of an object in topological order (fanins first)
static void Pdr2_ManSimCone_rec( Aig_Man_t * pAig, Aig_Obj_t * pObj, int * pTrav, int nTrav, Vec_Int_t * vCone )
{
    if ( pTrav[Aig_ObjId(pObj)] == nTrav )
        return;
    pTrav[Aig_ObjId(pObj)] = nTrav;
    if ( Aig_ObjIsNode(pObj) )
    {
        Pdr2_ManSimCone_rec( pAig, Aig_ObjFanin0(pObj), pTrav, nTrav, vCone );
        Pdr2_ManSimCone_rec( pAig, Aig_ObjFanin1(pObj), pTrav, nTrav, vCone );
    }
    else if ( Aig_ObjIsCo(pObj) )
        Pdr2_ManSimCone_rec( pAig, Aig_ObjFanin0(pObj), pTrav, nTrav, vCone );
    Vec_IntPush( vCone, Aig_ObjId(pObj) );
}
// ternary simulation of the collected cone (the CI values must be set)
static void Pdr2_ManSimCone( Pdr2_Man_t * p, char * pVals )
{
    Aig_Obj_t * pObj;
    int i, Id, v0, v1;
    pVals[Aig_ObjId(Aig_ManConst1(p->pAig))] = PDR2_V1;
    Vec_IntForEachEntry( p->vLiftCone, Id, i )
    {
        pObj = Aig_ManObj( p->pAig, Id );
        if ( Aig_ObjIsNode(pObj) )
        {
            v0 = Pdr2_ValNot( pVals[Aig_ObjFaninId0(pObj)], Aig_ObjFaninC0(pObj) );
            v1 = Pdr2_ValNot( pVals[Aig_ObjFaninId1(pObj)], Aig_ObjFaninC1(pObj) );
            pVals[Id] = (v0 == PDR2_V0 || v1 == PDR2_V0) ? PDR2_V0 : (v0 == PDR2_V1 && v1 == PDR2_V1) ? PDR2_V1 : PDR2_VX;
        }
        else if ( Aig_ObjIsCo(pObj) )
            pVals[Id] = Pdr2_ValNot( pVals[Aig_ObjFaninId0(pObj)], Aig_ObjFaninC0(pObj) );
    }
}

/**Function*************************************************************

  Synopsis    [Weakens the predecessor state by justification and ternary simulation.]

  Description [This is treb's weakening of proof obligations. vCube holds
  the latch literals of the model (after flipping), vInputs the input
  literals; the targets are the next-state literals of the last relative
  query (p->vRelInd) or the bad output. The frame is simulated with these
  values and the targets are justified structurally (for an AND with
  value 0 the fanin with value 0 of lower level is chosen); the latches
  outside the justification cone are dropped. Then each remaining latch,
  in the order of activity, is set to unknown and stays unknown if the
  targets keep their values. The latches with known values form the
  weakened cube, which still implies the targets with the inputs.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pdr2_ManSimWeaken( Pdr2_Man_t * p, Vec_Int_t * vCube, Vec_Int_t * vInputs )
{
    Aig_Man_t * pAig = p->pAig;
    Aig_Obj_t * pObj, * pFan0, * pFan1;
    char * pVals, * pMark, * pPi;
    Vec_Int_t * vJust, * vUndo, * vWork, * vVisit;
    int nObjs = Aig_ManObjNumMax( pAig );
    int i, k, Lit, Id, Id0, Id1, v0, v1, fBad, nTargets, fOk = 1;
    if ( p->pLiftVals == NULL )
    {
        p->pLiftVals  = ABC_ALLOC( char, nObjs );
        p->pLiftMark  = ABC_CALLOC( char, nObjs );
        p->pLiftPi    = ABC_CALLOC( char, Abc_MaxInt(1, p->nPis) );
        p->pLiftTrav  = ABC_CALLOC( int, nObjs );
        p->vLiftCone  = Vec_IntAlloc( 1000 );
        p->vLiftUndo  = Vec_IntAlloc( 1000 );
        p->vLiftWork  = Vec_IntAlloc( 1000 );
        p->vLiftJust  = Vec_IntAlloc( 1000 );
        p->vLiftVisit = Vec_IntAlloc( 1000 );
        if ( pAig->pFanData == NULL )
            Aig_ManFanoutStart( pAig );
    }
    pVals = p->pLiftVals; pMark = p->pLiftMark; pPi = p->pLiftPi;
    vJust = p->vLiftJust; vUndo = p->vLiftUndo; vWork = p->vLiftWork; vVisit = p->vLiftVisit;
    Vec_IntClear( vJust );
    Vec_IntClear( vUndo );
    Vec_IntClear( vWork );
    Vec_IntClear( vVisit );
    // values of the model; unassigned inputs and latches outside the cube take 0 (the model's
    // partial assignment satisfies every clause, so it determines the targets whatever they are)
    Aig_ManForEachCi( pAig, pObj, i )
        pVals[Aig_ObjId(pObj)] = PDR2_V0;
    Vec_IntForEachEntry( vInputs, Lit, i )
    {
        pVals[Aig_ObjId(Aig_ManCi(pAig, Abc_Lit2Var(Lit)))] = !Abc_LitIsCompl(Lit);
        pPi[Abc_Lit2Var(Lit)] = 1;
    }
    Vec_IntForEachEntry( vCube, Lit, i )
        pVals[Aig_ObjId(Saig_ManLo(pAig, Abc_Lit2Var(Lit)))] = !Abc_LitIsCompl(Lit);
    // the targets and their cone
    fBad = Vec_IntSize(p->vLastAssump) == 1 && Vec_IntEntry(p->vLastAssump, 0) == Abc_Var2Lit( p->VarBad, 0 );
    if ( fBad )
    {
        Id = Aig_ObjId( Aig_ManCo(pAig, 0) );
        pMark[Id] = 1;
        Vec_IntPush( vVisit, Id );
    }
    else
    {
        Vec_IntForEachEntry( p->vRelInd, Lit, i )
        {
            Id = Aig_ObjId( Saig_ManLi(pAig, Abc_Lit2Var(Lit)) );
            pMark[Id] = 1;
            Vec_IntPush( vVisit, Id );
        }
    }
    Vec_IntClear( p->vLiftCone );
    p->nLiftTrav++;
    Vec_IntForEachEntry( vVisit, Id, i )
        Pdr2_ManSimCone_rec( pAig, Aig_ManObj(pAig, Id), p->pLiftTrav, p->nLiftTrav, p->vLiftCone );
    Pdr2_ManSimCone( p, pVals );
    if ( fBad )
        fOk = pVals[Aig_ObjId(Aig_ManCo(pAig, 0))] == PDR2_V1;
    else
        Vec_IntForEachEntry( p->vRelInd, Lit, i )
            if ( pVals[Aig_ObjId(Saig_ManLi(pAig, Abc_Lit2Var(Lit)))] != (!Abc_LitIsCompl(Lit)) )
                fOk = 0;
    if ( !fOk )
    {
        // the simulation does not reproduce the model (should not happen): no weakening
        p->nLiftSimFail++;
        goto finish;
    }
    // justification from the targets: the fanins of a 1-node, one 0-fanin of a 0-node
    nTargets = Vec_IntSize( vVisit );
    for ( i = 0; i < nTargets; i++ )
    {
        Id  = Vec_IntEntry( vVisit, i );
        Id0 = Aig_ObjFaninId0( Aig_ManObj(pAig, Id) );
        if ( !pMark[Id0] )
        {
            pMark[Id0] = 2;
            Vec_IntPush( vVisit, Id0 );
            Vec_IntPush( vWork, Id0 );
        }
    }
    while ( Vec_IntSize(vWork) > 0 )
    {
        Id = Vec_IntPop( vWork );
        pObj = Aig_ManObj( pAig, Id );
        if ( Aig_ObjIsCi(pObj) )
        {
            if ( Aig_ObjCioId(pObj) >= Saig_ManPiNum(pAig) )
                Vec_IntPush( vJust, Aig_ObjCioId(pObj) - Saig_ManPiNum(pAig) );
            else if ( !pPi[Aig_ObjCioId(pObj)] )
            {
                // an input unassigned in the model is used with value 0
                Vec_IntPush( vInputs, Abc_Var2Lit( Aig_ObjCioId(pObj), 1 ) );
                pPi[Aig_ObjCioId(pObj)] = 1;
            }
            continue;
        }
        if ( !Aig_ObjIsNode(pObj) )
            continue;
        pFan0 = Aig_ObjFanin0( pObj );
        pFan1 = Aig_ObjFanin1( pObj );
        Id0 = Aig_ObjId( pFan0 );
        Id1 = Aig_ObjId( pFan1 );
        if ( pVals[Id] == PDR2_V1 )
        {
            if ( !pMark[Id0] ) { pMark[Id0] = 2; Vec_IntPush( vVisit, Id0 ); Vec_IntPush( vWork, Id0 ); }
            if ( !pMark[Id1] ) { pMark[Id1] = 2; Vec_IntPush( vVisit, Id1 ); Vec_IntPush( vWork, Id1 ); }
            continue;
        }
        assert( pVals[Id] == PDR2_V0 );
        v0 = Pdr2_ValNot( pVals[Id0], Aig_ObjFaninC0(pObj) );
        v1 = Pdr2_ValNot( pVals[Id1], Aig_ObjFaninC1(pObj) );
        if ( (v0 == PDR2_V0 && pMark[Id0]) || (v1 == PDR2_V0 && pMark[Id1]) )
            continue;
        if ( v0 == PDR2_V0 && (v1 != PDR2_V0 || Aig_ObjLevel(pFan0) <= Aig_ObjLevel(pFan1)) )
            { pMark[Id0] = 2; Vec_IntPush( vVisit, Id0 ); Vec_IntPush( vWork, Id0 ); }
        else
        {
            assert( v1 == PDR2_V0 );
            pMark[Id1] = 2; Vec_IntPush( vVisit, Id1 ); Vec_IntPush( vWork, Id1 );
        }
    }
    // the latches outside the justification cone become unknown
    Saig_ManForEachLo( pAig, pObj, i )
        if ( pMark[Aig_ObjId(pObj)] != 2 )
            pVals[Aig_ObjId(pObj)] = PDR2_VX;
    Pdr2_ManSimCone( p, pVals );
    // removal trials in the order of activity
    Vec_IntClear( vWork );
    Vec_IntForEachEntry( vJust, k, i )
        Vec_IntPush( vWork, Abc_Var2Lit( k, pVals[Aig_ObjId(Saig_ManLo(pAig, k))] == PDR2_V0 ) );
    if ( p->pPars->nLiftSimOrder == 2 )
        Vec_IntSort( vWork, 0 );
    else
        Pdr2_ManSortByAct( p, vWork, p->pPars->nLiftSimOrder == 1 );
    Vec_IntClear( vJust );
    Vec_IntAppend( vJust, vWork );
    Vec_IntForEachEntry( vJust, Lit, i )
    {
        // at the deadline the remaining trials are skipped (their literals stay in the cube)
        if ( (i & 63) == 63 && Pdr2_ManPastDeadline(p) )
        {
            p->nLiftSimCut++;
            break;
        }
        Id = Aig_ObjId( Saig_ManLo(pAig, Abc_Lit2Var(Lit)) );
        if ( Pdr2_ManSimXProp1( p, pVals, pMark, vUndo, vWork, Id, PDR2_VX ) )
            Vec_IntClear( vUndo );
        else
            Pdr2_ManSimXUndo1( pVals, vUndo );
    }
    // the result
    Vec_IntClear( vCube );
    Vec_IntForEachEntry( vJust, Lit, i )
        if ( pVals[Aig_ObjId(Saig_ManLo(pAig, Abc_Lit2Var(Lit)))] != PDR2_VX )
            Vec_IntPush( vCube, Lit );
finish:
    Vec_IntForEachEntry( vVisit, Id, i )
        pMark[Id] = 0;
    Vec_IntForEachEntry( vInputs, Lit, i )
        pPi[Abc_Lit2Var(Lit)] = 0;
}

/**Function*************************************************************

  Synopsis    [Simulates the input trace of the obligation chain concretely.]

  Description [Returns 1 if the property fails at the last frame, that is,
  the counterexample is real, and -1 at the deadline.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pdr2_ManAbsSimConcrete( Pdr2_Man_t * p, Pdr2_Obl_t * pObl )
{
    Aig_Obj_t * pObj;
    char * pVals = p->pAbsVals, * pNext = p->pAbsVals + Aig_ManObjNumMax(p->pAig);
    Pdr2_Obl_t * pTemp;
    int i, Lit, Result;
    // the initial state (computed by the caller for the head of the chain)
    Saig_ManForEachLo( p->pAig, pObj, i )
        pVals[Aig_ObjId(pObj)] = p->pInitState[i];
    for ( pTemp = pObl; pTemp; pTemp = pTemp->pNext )
    {
        if ( Pdr2_ManPastDeadline(p) )
            return -1;
        Saig_ManForEachPi( p->pAig, pObj, i )
            pVals[Aig_ObjId(pObj)] = PDR2_V0;
        Vec_IntForEachEntry( pTemp->vInputs, Lit, i )
            pVals[Aig_ObjId(Aig_ManCi(p->pAig, Abc_Lit2Var(Lit)))] = !Abc_LitIsCompl(Lit);
        Pdr2_ManAbsSimFrame( p, pVals );
        if ( pTemp->pNext == NULL )
            break;
        Saig_ManForEachLi( p->pAig, pObj, i )
            pNext[i] = pVals[Aig_ObjId(pObj)];
        Saig_ManForEachLo( p->pAig, pObj, i )
            pVals[Aig_ObjId(pObj)] = pNext[i];
    }
    Result = pVals[Aig_ObjId(Aig_ManCo(p->pAig, 0))] == PDR2_V1;
    return Result;
}

/**Function*************************************************************

  Synopsis    [Refinement by ternary simulation of the abstract trace.]

  Description [The flops outside the abstraction take their recorded
  values (unknown where none is recorded); the trace must fail the
  property. Then, frame by frame from the last one, each recorded value
  is replaced by unknown: if the property output stays 1, the value was
  not needed; otherwise it is restored and the flop joins the abstraction.
  This is the refinement used by treb -abs. Returns 0 if the simulation
  does not reproduce the failure (the caller falls back to justification)
  and -1 at the deadline (the abstraction is then unchanged).]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Pdr2_ManAbsSimFrames( Pdr2_Man_t * p, char * pVals, char * pFix, int nObjs, int fStart, int nFrames, Vec_Ptr_t * vInputs )
{
    Aig_Obj_t * pObj;
    int f, i, Lit, Id;
    for ( f = fStart; f < nFrames; f++ )
    {
        char * pV = pVals + (size_t)f * nObjs;
        Vec_Int_t * vIn = (Vec_Int_t *)Vec_PtrEntry( vInputs, f );
        Saig_ManForEachPi( p->pAig, pObj, i )
            pV[Aig_ObjId(pObj)] = PDR2_V0;
        Vec_IntForEachEntry( vIn, Lit, i )
            pV[Aig_ObjId(Aig_ManCi(p->pAig, Abc_Lit2Var(Lit)))] = !Abc_LitIsCompl(Lit);
        // flops with a recorded (or trial) value keep it; all others follow the previous frame
        // (the initial state in frame 0), so the trace is concrete everywhere else
        Saig_ManForEachLo( p->pAig, pObj, i )
        {
            Id = Aig_ObjId( pObj );
            if ( pFix && pFix[(size_t)f * p->nRegs + i] )
                continue;
            if ( f == 0 )
                pV[Id] = p->pInitState[i];
            else
                pV[Id] = pVals[(size_t)(f-1) * nObjs + Aig_ObjId(Saig_ManLi(p->pAig, i))];
        }
        Pdr2_ManAbsSimFrame( p, pV );
    }
    return pVals[(size_t)(nFrames-1) * nObjs + Aig_ObjId(Aig_ManCo(p->pAig, 0))];
}
// incremental ternary propagation of one changed value in the simulated trace (as treb's
// XSimulate::propagate): flops in the abstraction and flops without a recorded pseudo-input
// value follow the previous frame, the recorded ones keep their values. Changed positions are recorded in vUndo (position, old value) for undoing.
// Returns 0 as soon as the property output of the last frame is no longer 1.
static int Pdr2_ManAbsXProp( Pdr2_Man_t * p, char * pVals, char * pFix, int nObjs, int nFrames, Vec_Int_t * vUndo, Vec_Int_t * vWork, int f, int Id, int Val )
{
    Aig_Man_t * pAig = p->pAig;
    Aig_Obj_t * pObj, * pFan;
    int iFan, k, Pos = f * nObjs + Id, Old, New, FanId, v0, v1, fOk = 1;
    if ( pVals[Pos] == Val )
        return 1;
    Vec_IntClear( vWork );
    Vec_IntPushTwo( vUndo, Pos, pVals[Pos] );
    pVals[Pos] = (char)Val;
    Vec_IntPushTwo( vWork, f, Id );
    while ( Vec_IntSize(vWork) > 0 && fOk )
    {
        char * pV;
        Id = Vec_IntPop( vWork );
        f  = Vec_IntPop( vWork );
        pV = pVals + (size_t)f * nObjs;
        pObj = Aig_ManObj( pAig, Id );
        Aig_ObjForEachFanout( pAig, pObj, pFan, iFan, k )
        {
            FanId = Aig_ObjId( pFan );
            Old = pV[FanId];
            if ( Aig_ObjIsNode(pFan) )
            {
                v0 = Pdr2_ValNot( pV[Aig_ObjFaninId0(pFan)], Aig_ObjFaninC0(pFan) );
                v1 = Pdr2_ValNot( pV[Aig_ObjFaninId1(pFan)], Aig_ObjFaninC1(pFan) );
                New = (v0 == PDR2_V0 || v1 == PDR2_V0) ? PDR2_V0 : (v0 == PDR2_V1 && v1 == PDR2_V1) ? PDR2_V1 : PDR2_VX;
                if ( New == Old )
                    continue;
                Vec_IntPushTwo( vUndo, f * nObjs + FanId, Old );
                pV[FanId] = (char)New;
                Vec_IntPushTwo( vWork, f, FanId );
                continue;
            }
            assert( Aig_ObjIsCo(pFan) );
            New = Pdr2_ValNot( pV[Aig_ObjFaninId0(pFan)], Aig_ObjFaninC0(pFan) );
            if ( New == Old )
                continue;
            Vec_IntPushTwo( vUndo, f * nObjs + FanId, Old );
            pV[FanId] = (char)New;
            if ( Aig_ObjCioId(pFan) < Saig_ManPoNum(pAig) )
            {
                if ( f == nFrames - 1 && New != PDR2_V1 )
                    fOk = 0;
            }
            else
            {
                int iReg = Aig_ObjCioId(pFan) - Saig_ManPoNum(pAig);
                // flops of the abstraction and flops without a recorded value follow the previous frame
                if ( f + 1 < nFrames && (p->pAbs[iReg] || !pFix[(size_t)(f + 1) * p->nRegs + iReg]) )
                {
                    int Pos2 = (f + 1) * nObjs + Aig_ObjId( Saig_ManLo(pAig, iReg) );
                    if ( pVals[Pos2] != New )
                    {
                        Vec_IntPushTwo( vUndo, Pos2, pVals[Pos2] );
                        pVals[Pos2] = (char)New;
                        Vec_IntPushTwo( vWork, f + 1, Aig_ObjId(Saig_ManLo(pAig, iReg)) );
                    }
                }
            }
        }
    }
    return fOk;
}
static void Pdr2_ManAbsXUndo( char * pVals, Vec_Int_t * vUndo, int Mark )
{
    int i;
    for ( i = Vec_IntSize(vUndo) - 2; i >= Mark; i -= 2 )
        pVals[Vec_IntEntry(vUndo, i)] = (char)Vec_IntEntry( vUndo, i + 1 );
    Vec_IntShrink( vUndo, Mark );
}
static int Pdr2_ManAbsRefineXsim( Pdr2_Man_t * p, Pdr2_Obl_t * pObl, int * pnRefined )
{
    Pdr2_Obl_t * pTemp;
    Vec_Ptr_t * vInputs = Vec_PtrAlloc( 100 ), * vPpis = Vec_PtrAlloc( 100 );
    Vec_Int_t * vLits;
    int nObjs = Aig_ManObjNumMax( p->pAig );
    int nFrames = pObl->nDepth + 1;
    char * pVals = ABC_ALLOC( char, (size_t)nFrames * nObjs );
    char * pFix = ABC_CALLOC( char, (size_t)nFrames * p->nRegs );
    Vec_Int_t * vUndo, * vWork;
    int IdBad = Aig_ObjId( Aig_ManCo(p->pAig, 0) );
    int f, i, Lit, Id, nRefined = 0, nTrials = 0, Result = 1;
    // collect the inputs and the recorded values of the flops outside the abstraction per frame
    for ( pTemp = pObl; pTemp; pTemp = pTemp->pNext )
    {
        Vec_PtrPush( vInputs, pTemp->vInputs );
        vLits = Vec_IntAlloc( 100 );
        for ( i = 0; i < pTemp->pState->nLits; i++ )
            if ( !p->pAbs[Abc_Lit2Var(pTemp->pState->Lits[i])] )
                Vec_IntPush( vLits, pTemp->pState->Lits[i] );
        Vec_IntForEachEntry( pTemp->vPpis, Lit, i )
            if ( !p->pAbs[Abc_Lit2Var(Lit)] )
                Vec_IntPush( vLits, Lit );
        Vec_PtrPush( vPpis, vLits );
    }
    // preset: recorded pseudo-inputs take their values; every other flop follows the simulation
    for ( f = 0; f < nFrames; f++ )
    {
        char * pV = pVals + (size_t)f * nObjs;
        Vec_IntForEachEntry( (Vec_Int_t *)Vec_PtrEntry(vPpis, f), Lit, i )
        {
            pV[Aig_ObjId(Saig_ManLo(p->pAig, Abc_Lit2Var(Lit)))] = !Abc_LitIsCompl(Lit);
            pFix[(size_t)f * p->nRegs + Abc_Lit2Var(Lit)] = 1;
        }
    }
    if ( Pdr2_ManAbsSimFrames( p, pVals, pFix, nObjs, 0, nFrames, vInputs ) != PDR2_V1 )
    {
        Result = 0;
        goto finish;
    }
    if ( Pdr2_ManPastDeadline(p) )
    {
        Result = -1;
        goto finish;
    }
    if ( p->pPars->nAbsRefineMode >= 1 )
    {
        // every flop outside the abstraction is a pseudo-input with its simulated value in every
        // frame (treb completes these values by SAT), so unknowns travel only through the abstraction
        for ( f = 0; f < nFrames; f++ )
            for ( i = 0; i < p->nRegs; i++ )
                if ( !p->pAbs[i] )
                    pFix[(size_t)f * p->nRegs + i] = 1;
    }
    // greedy minimization, frame by frame from the last one: each recorded pseudo-input value
    // is set to unknown with incremental ternary propagation; if the property output stays 1
    // the value was not needed, otherwise it is restored and the flop joins the abstraction
    if ( p->pAig->pFanData == NULL )
        Aig_ManFanoutStart( p->pAig );
    vUndo = Vec_IntAlloc( 1000 );
    vWork = Vec_IntAlloc( 1000 );
    if ( p->pPars->nAbsRefineMode >= 2 )
    {
        // treb's loop: every flop outside the abstraction, from the last frame to the first;
        // the flop joins the abstraction at the first frame where its value is needed
        for ( i = 0; i < p->nRegs && Result != -1; i++ )
        {
            if ( p->pAbs[i] )
                continue;
            Id = Aig_ObjId( Saig_ManLo(p->pAig, i) );
            for ( f = nFrames - 1; f >= 0 && Result != -1; f-- )
            {
                int fNeeded, e;
                if ( pVals[(size_t)f * nObjs + Id] == PDR2_VX )
                    continue;
                if ( (++nTrials & 63) == 0 && Pdr2_ManPastDeadline(p) )
                {
                    Result = -1;
                    break;
                }
                fNeeded = !Pdr2_ManAbsXProp( p, pVals, pFix, nObjs, nFrames, vUndo, vWork, f, Id, PDR2_VX );
                if ( !fNeeded && p->pPars->nAbsRefineMode == 3 )
                {
                    // treb also keeps the property output of the intermediate frames known
                    for ( e = 0; e < Vec_IntSize(vUndo); e += 2 )
                        if ( Vec_IntEntry(vUndo, e) % nObjs == IdBad )
                        {
                            fNeeded = 1;
                            break;
                        }
                }
                if ( !fNeeded )
                {
                    Vec_IntClear( vUndo );
                    continue;
                }
                Pdr2_ManAbsXUndo( pVals, vUndo, 0 );
                p->pAbsUsed[i] = 1;
                nRefined++;
                break;
            }
        }
    }
    else
    for ( f = nFrames - 1; f >= 0 && Result != -1; f-- )
    {
        Vec_IntForEachEntry( (Vec_Int_t *)Vec_PtrEntry(vPpis, f), Lit, i )
        {
            if ( p->pAbsUsed[Abc_Lit2Var(Lit)] )
                continue; // already known to be needed in a later frame
            Id = Aig_ObjId( Saig_ManLo(p->pAig, Abc_Lit2Var(Lit)) );
            if ( pVals[(size_t)f * nObjs + Id] == PDR2_VX )
                continue;
            if ( (++nTrials & 63) == 0 && Pdr2_ManPastDeadline(p) )
            {
                Result = -1;
                break;
            }
            if ( Pdr2_ManAbsXProp( p, pVals, pFix, nObjs, nFrames, vUndo, vWork, f, Id, PDR2_VX ) )
            {
                Vec_IntClear( vUndo );
                continue;
            }
            Pdr2_ManAbsXUndo( pVals, vUndo, 0 );
            p->pAbsUsed[Abc_Lit2Var(Lit)] = 1;
            nRefined++;
        }
    }
    Vec_IntFree( vUndo );
    Vec_IntFree( vWork );
    // (canceled: the marks are cleared and the abstraction stays as it was)
    for ( i = 0; i < p->nRegs; i++ )
        if ( p->pAbsUsed[i] )
        {
            p->pAbsUsed[i] = 0;
            if ( Result != -1 && !p->pAbs[i] )
            {
                p->pAbs[i] = 1;
                p->nAbsFlops++;
            }
        }
    if ( Result == -1 )
        goto finish;
    if ( nRefined == 0 )
        Result = 0;
    *pnRefined = nRefined;
finish:
    Vec_PtrForEachEntry( Vec_Int_t *, vPpis, vLits, i )
        Vec_IntFree( vLits );
    Vec_PtrFree( vPpis );
    Vec_PtrFree( vInputs );
    ABC_FREE( pVals );
    ABC_FREE( pFix );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Checks the abstract counterexample and refines if spurious.]

  Description [The chain of obligations is a counterexample of the
  abstract model in which the flops outside the abstraction are free
  inputs taking the recorded values. If its inputs do not fail the
  property concretely, the abstract trace is simulated with all values
  concrete, and a backward justification of the failing output selects
  the pseudo-inputs it depends on; their flops join the abstraction.
  Justification prefers real inputs over recorded pseudo-inputs and
  recorded pseudo-inputs over arbitrary ones. Returns 1 if the
  counterexample is real, and -1 if the deadline canceled the check (the
  abstraction is then unchanged).]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pdr2_ManAbsCheckCex( Pdr2_Man_t * p, Pdr2_Obl_t * pObl )
{
    Aig_Obj_t * pObj;
    Pdr2_Obl_t * pTemp;
    int nObjs = Aig_ManObjNumMax( p->pAig );
    int nFrames = pObl->nDepth + 1;
    char * pVals = NULL, * pMark = NULL;
    unsigned short * pPrio = NULL;
    int f, i, Lit, Id, v0, v1, p0, p1, nRefined = 0, RetValue;
    abctime clk = Abc_Clock();
    // the initial state of the trace: the one the counterexample will have
    Pdr2_ManInitState( p, pObl->pState, p->pInitState );
    if ( (RetValue = Pdr2_ManAbsSimConcrete( p, pObl )) )
    {
        p->nAbsCut += RetValue == -1;
        return RetValue;
    }
    // a chain created before a fixup of the abstraction (Pdr2_ManAbsProject) has recorded
    // pseudo-input values of a flop that is now in the abstraction: it is no longer an
    // abstract trace and is discarded (the caller restarts from the bad states)
    for ( pTemp = pObl; pTemp; pTemp = pTemp->pNext )
        Vec_IntForEachEntry( pTemp->vPpis, Lit, i )
            if ( p->pAbs[Abc_Lit2Var(Lit)] )
            {
                p->nAbsStale++;
                p->timeAbs += Abc_Clock() - clk;
                return 0;
            }
    p->nAbsCexes++;
    if ( p->pPars->fAbsRefineAll )
    {
        // simple refinement: all flops with recorded pseudo-input values join the abstraction
        for ( pTemp = pObl; pTemp; pTemp = pTemp->pNext )
            Vec_IntForEachEntry( pTemp->vPpis, Lit, i )
                if ( !p->pAbs[Abc_Lit2Var(Lit)] )
                {
                    p->pAbs[Abc_Lit2Var(Lit)] = 1;
                    p->nAbsFlops++;
                    nRefined++;
                }
        p->nAbsRefined += nRefined;
        if ( p->pPars->fVeryVerbose )
        {
            Abc_Print( 1, "Spurious counterexample of length %d at level %d: refined %d flops (abstraction has %d of %d flops). Frames:",
                nFrames, Pdr2_ManLevel(p), nRefined, p->nAbsFlops, p->nRegs );
            for ( pTemp = pObl; pTemp; pTemp = pTemp->pNext )
                Abc_Print( 1, " %d", pTemp->iFrame );
            Abc_Print( 1, "\n" );
        }
        p->timeAbs += Abc_Clock() - clk;
        return 0;
    }
    // the incremental simulation keeps trace positions as int (in its undo log): longer traces
    // go straight to the justification, whose offsets are size_t
    if ( p->pPars->fAbsRefineXsim && (ABC_INT64_T)nFrames * nObjs < (ABC_INT64_T)0x7fffffff && (RetValue = Pdr2_ManAbsRefineXsim( p, pObl, &nRefined )) )
    {
        if ( RetValue == -1 )
            goto cut;
        p->nAbsXsimRefs++;
        goto finish;
    }
    // simulate the abstract trace with concrete values and compute priorities
    pVals = ABC_ALLOC( char, (size_t)nFrames * nObjs );
    pMark = ABC_CALLOC( char, (size_t)nFrames * nObjs );
    pPrio = ABC_ALLOC( unsigned short, (size_t)nFrames * nObjs );
    for ( pTemp = pObl, f = 0; pTemp; pTemp = pTemp->pNext, f++ )
    {
        char * pV = pVals + (size_t)f * nObjs;
        unsigned short * pP = pPrio + (size_t)f * nObjs;
        if ( Pdr2_ManPastDeadline(p) )
            goto cut;
        // inputs
        Saig_ManForEachPi( p->pAig, pObj, i )
        {
            pV[Aig_ObjId(pObj)] = PDR2_V0;
            pP[Aig_ObjId(pObj)] = 0;
        }
        Vec_IntForEachEntry( pTemp->vInputs, Lit, i )
            pV[Aig_ObjId(Aig_ManCi(p->pAig, Abc_Lit2Var(Lit)))] = !Abc_LitIsCompl(Lit);
        // flops: abstracted ones are free (arbitrary value 0), others follow the previous frame
        Saig_ManForEachLo( p->pAig, pObj, i )
        {
            Id = Aig_ObjId( pObj );
            if ( f == 0 )
            {
                pV[Id] = p->pInitState[i];
                pP[Id] = 0;
            }
            else if ( p->pAbs[i] )
            {
                int IdLi = Aig_ObjId( Saig_ManLi(p->pAig, i) );
                pV[Id] = pVals[(size_t)(f-1) * nObjs + IdLi];
                pP[Id] = pPrio[(size_t)(f-1) * nObjs + IdLi];
            }
            else
            {
                pV[Id] = PDR2_V0;
                pP[Id] = PDR2_PRIO_PPI_FREE;
            }
        }
        // recorded values of the flops outside the abstraction (from the state cube and the pseudo-inputs)
        for ( i = 0; i < pTemp->pState->nLits + Vec_IntSize(pTemp->vPpis); i++ )
        {
            Lit = i < pTemp->pState->nLits ? pTemp->pState->Lits[i] : Vec_IntEntry( pTemp->vPpis, i - pTemp->pState->nLits );
            if ( p->pAbs[Abc_Lit2Var(Lit)] )
                continue;
            // (at frame 0 the abstracted flops take the recorded values, not the initial ones)
            Id = Aig_ObjId( Saig_ManLo(p->pAig, Abc_Lit2Var(Lit)) );
            pV[Id] = !Abc_LitIsCompl(Lit);
            pP[Id] = 1;
        }
        // nodes
        pV[Aig_ObjId(Aig_ManConst1(p->pAig))] = PDR2_V1;
        pP[Aig_ObjId(Aig_ManConst1(p->pAig))] = 0;
        Aig_ManForEachNode( p->pAig, pObj, i )
        {
            v0 = pV[Aig_ObjFaninId0(pObj)] ^ Aig_ObjFaninC0(pObj);
            v1 = pV[Aig_ObjFaninId1(pObj)] ^ Aig_ObjFaninC1(pObj);
            p0 = pP[Aig_ObjFaninId0(pObj)];
            p1 = pP[Aig_ObjFaninId1(pObj)];
            if ( v0 == PDR2_V1 && v1 == PDR2_V1 )
            {
                pV[i] = PDR2_V1;
                pP[i] = (unsigned short)Abc_MaxInt( p0, p1 );
            }
            else
            {
                pV[i] = PDR2_V0;
                if ( v0 == PDR2_V0 && v1 == PDR2_V0 )
                    pP[i] = (unsigned short)Abc_MinInt( p0, p1 );
                else
                    pP[i] = (unsigned short)(v0 == PDR2_V0 ? p0 : p1);
            }
        }
        Aig_ManForEachCo( p->pAig, pObj, i )
        {
            pV[Aig_ObjId(pObj)] = pV[Aig_ObjFaninId0(pObj)] ^ Aig_ObjFaninC0(pObj);
            pP[Aig_ObjId(pObj)] = pP[Aig_ObjFaninId0(pObj)];
        }
    }
    assert( f == nFrames );
    if ( pVals[(size_t)(nFrames-1) * nObjs + Aig_ObjId(Aig_ManCo(p->pAig, 0))] != PDR2_V1 )
    {
        Abc_Print( 1, "Pdr2_ManAbsCheckCex(): Internal error: the abstract trace does not fail the property.\n" );
        // refine with all recorded pseudo-inputs
        for ( pTemp = pObl; pTemp; pTemp = pTemp->pNext )
            Vec_IntForEachEntry( pTemp->vPpis, Lit, i )
                if ( !p->pAbs[Abc_Lit2Var(Lit)] )
                {
                    p->pAbs[Abc_Lit2Var(Lit)] = 1;
                    p->nAbsFlops++;
                    nRefined++;
                }
        goto finish;
    }
    // backward justification from the failing output
    pMark[(size_t)(nFrames-1) * nObjs + Aig_ObjId(Aig_ManCo(p->pAig, 0))] = 1;
    for ( f = nFrames - 1; f >= 0; f-- )
    {
        char * pV = pVals + (size_t)f * nObjs;
        char * pM = pMark + (size_t)f * nObjs;
        unsigned short * pP = pPrio + (size_t)f * nObjs;
        if ( Pdr2_ManPastDeadline(p) )
        {
            for ( i = 0; i < p->nRegs; i++ )
                p->pAbsUsed[i] = 0;
            goto cut;
        }
        Aig_ManForEachCo( p->pAig, pObj, i )
            if ( pM[Aig_ObjId(pObj)] )
                pM[Aig_ObjFaninId0(pObj)] = 1;
        Aig_ManForEachNodeReverse( p->pAig, pObj, i )
        {
            if ( !pM[i] )
                continue;
            if ( pV[i] == PDR2_V1 )
            {
                pM[Aig_ObjFaninId0(pObj)] = 1;
                pM[Aig_ObjFaninId1(pObj)] = 1;
                continue;
            }
            v0 = pV[Aig_ObjFaninId0(pObj)] ^ Aig_ObjFaninC0(pObj);
            v1 = pV[Aig_ObjFaninId1(pObj)] ^ Aig_ObjFaninC1(pObj);
            if ( v0 == PDR2_V0 && v1 == PDR2_V0 )
            {
                if ( pP[Aig_ObjFaninId0(pObj)] <= pP[Aig_ObjFaninId1(pObj)] )
                    pM[Aig_ObjFaninId0(pObj)] = 1;
                else
                    pM[Aig_ObjFaninId1(pObj)] = 1;
            }
            else if ( v0 == PDR2_V0 )
                pM[Aig_ObjFaninId0(pObj)] = 1;
            else
                pM[Aig_ObjFaninId1(pObj)] = 1;
        }
        // marked flops: abstracted ones are needed pseudo-inputs, others continue to the previous frame
        Saig_ManForEachLo( p->pAig, pObj, i )
        {
            if ( !pM[Aig_ObjId(pObj)] )
                continue;
            if ( p->pAbs[i] )
            {
                if ( f > 0 )
                    pMark[(size_t)(f-1) * nObjs + Aig_ObjId(Saig_ManLi(p->pAig, i))] = 1;
            }
            else if ( !p->pAbsUsed[i] )
            {
                p->pAbsUsed[i] = 1; // temporary mark: refined in this round
                nRefined++;
            }
        }
    }
    for ( i = 0; i < p->nRegs; i++ )
        if ( p->pAbsUsed[i] )
        {
            p->pAbsUsed[i] = 0;
            if ( !p->pAbs[i] )
            {
                p->pAbs[i] = 1;
                p->nAbsFlops++;
            }
        }
    if ( nRefined == 0 )
    {
        Abc_Print( 1, "Pdr2_ManAbsCheckCex(): Internal error: a spurious counterexample without pseudo-inputs.\n" );
        for ( pTemp = pObl; pTemp; pTemp = pTemp->pNext )
            Vec_IntForEachEntry( pTemp->vPpis, Lit, i )
                if ( !p->pAbs[Abc_Lit2Var(Lit)] )
                {
                    p->pAbs[Abc_Lit2Var(Lit)] = 1;
                    p->nAbsFlops++;
                    nRefined++;
                }
    }
finish:
    p->nAbsRefined += nRefined;
    if ( p->pPars->fVeryVerbose )
    {
        Abc_Print( 1, "Spurious counterexample of length %d at level %d: refined %d flops (abstraction has %d of %d flops). Frames:",
            nFrames, Pdr2_ManLevel(p), nRefined, p->nAbsFlops, p->nRegs );
        for ( pTemp = pObl; pTemp; pTemp = pTemp->pNext )
            Abc_Print( 1, " %d", pTemp->iFrame );
        Abc_Print( 1, "\n" );
    }
    ABC_FREE( pVals );
    ABC_FREE( pMark );
    ABC_FREE( pPrio );
    p->timeAbs += Abc_Clock() - clk;
    return 0;
cut:
    p->nAbsCut++;
    ABC_FREE( pVals );
    ABC_FREE( pMark );
    ABC_FREE( pPrio );
    p->timeAbs += Abc_Clock() - clk;
    return -1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
