/**CFile****************************************************************

  FileName    [imcUnroll.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Interpolation-based model checking.]

  Synopsis    [Incremental mapped CNF for bounded transition unrolling.]

  Author      [ABC contributors]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 23, 2026.]

  Revision    [$Id: imcUnroll.c,v 1.00 2026/10/23 00:00:00 alanmi Exp $]

***********************************************************************/

#include "imcInt.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

struct Imc_Unr_t_
{
    Gia_Man_t * pGia;
    Vec_Int_t * vState, * vInputs, * vResets, * vBad, * vVars;
    int nFrames, nVars, iFail;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Releases the persistent bounded-transition unroller.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Imc_ManUnrollStop( Imc_Man_t * p )
{
    Imc_Unr_t * pUnroll = p->pUnroll;
    if ( pUnroll == NULL ) return;
    Gia_ManStop( pUnroll->pGia );
    Vec_IntFree( pUnroll->vState );
    Vec_IntFree( pUnroll->vInputs );
    Vec_IntFree( pUnroll->vResets );
    Vec_IntFree( pUnroll->vBad );
    Vec_IntFree( pUnroll->vVars );
    ABC_FREE( p->pUnroll );
}

/**Function*************************************************************

  Synopsis    [Adds a primary input to the persistent unrolling.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_UnrInput( Imc_Unr_t * pUnroll )
{
    int Lit = Gia_ManAppendCi( pUnroll->pGia );
    Vec_IntFillExtra( pUnroll->vVars, Gia_ManObjNum(pUnroll->pGia), -1 );
    Vec_IntWriteEntry( pUnroll->vVars, Abc_Lit2Var(Lit), Abc_Var2Lit(pUnroll->nVars++, 0) );
    return Lit;
}

/**Function*************************************************************

  Synopsis    [Initializes the direction-specific bounded-transition unroller.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Imc_Unr_t * Imc_UnrStart( Imc_Man_t * p )
{
    Imc_Unr_t * pUnroll = ABC_CALLOC( Imc_Unr_t, 1 );
    int i;
    pUnroll->pGia = Gia_ManStart( Gia_ManObjNum(p->pGia) );
    pUnroll->pGia->fAddStrash = 1;
    Gia_ManHashStart( pUnroll->pGia );
    pUnroll->vState = Vec_IntAlloc( Gia_ManRegNum(p->pGia) );
    pUnroll->vInputs = Vec_IntAlloc( 128 );
    pUnroll->vResets = Vec_IntAlloc( 32 );
    pUnroll->vBad = Vec_IntAlloc( 32 );
    pUnroll->vVars = Vec_IntAlloc( 128 );
    // SAT variable zero represents the constant-false unrolling node.
    Vec_IntPush( pUnroll->vVars, 0 );
    pUnroll->nVars = 1;
    for ( i = 0; i < Gia_ManRegNum(p->pGia); i++ )
        Vec_IntPush( pUnroll->vState, p->pPars->fBackward ? 0 : Imc_UnrInput(pUnroll) );
    pUnroll->nFrames = p->pPars->fBackward;
    if ( p->pCnfB ) Cnf_DataFree( p->pCnfB );
    p->pCnfB = Cnf_DataAlloc( NULL, pUnroll->nVars, 1, 1 );
    p->pCnfB->pClauses[0][0] = 1;
    Vec_IntFreeP( &p->vCnfStartB );
    Vec_IntFreeP( &p->vCnfCountB );
    Imc_CnfMap( p->pCnfB, &p->vCnfStartB, &p->vCnfCountB );
    return pUnroll;
}

// Map only cones whose definitions are absent from the accumulated CNF.
// Previously mapped nodes become inputs of this chunk, with stable SAT IDs.
/**Function*************************************************************

  Synopsis    [Adds unmapped transition cones while preserving existing SAT variable identifiers.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Imc_UnrEncode( Imc_Man_t * p, Vec_Int_t * vRoots )
{
    Imc_Unr_t * pUnroll = p->pUnroll;
    Gia_Man_t * pChunk = Gia_ManStart( 1024 );
    Aig_Man_t * pAig = NULL;
    Cnf_Dat_t * pCnf = NULL, * pOld = p->pCnfB, * pNext;
    Vec_Int_t * vStack = Vec_IntAlloc( 128 ), * vNodes = Vec_IntAlloc( 1024 );
    Vec_Int_t * vOrigin = Vec_IntAlloc( 1024 ), * vMap = NULL, * vResult = NULL;
    Vec_Str_t * vSeen = Vec_StrStart( Gia_ManObjNum(pUnroll->pGia) ), * vSkip = NULL;
    Gia_Obj_t * pObj;
    int i, k, Id, Lit, Var, nClauses = 0, nLits = 0, Offset, Out, * pLit;
    Vec_IntFillExtra( pUnroll->vVars, Gia_ManObjNum(pUnroll->pGia), -1 );
    Vec_IntForEachEntry( vRoots, Lit, i )
        Vec_IntPush( vStack, Abc_Lit2Var(Lit) );
    while ( Vec_IntSize(vStack) )
    {
        Id = Vec_IntPop( vStack );
        if ( Vec_StrEntry(vSeen, Id) ) continue;
        Vec_StrWriteEntry( vSeen, Id, 1 );
        Vec_IntPush( vNodes, Id );
        if ( (Vec_IntSize(vNodes) & 1023) == 0 && p->TimeStop && Abc_Clock() >= p->TimeStop )
            goto finish;
        if ( Vec_IntEntry(pUnroll->vVars, Id) >= 0 ) continue;
        pObj = Gia_ManObj( pUnroll->pGia, Id );
        assert( Gia_ObjIsAnd(pObj) );
        Vec_IntPush( vStack, Gia_ObjFaninId0p(pUnroll->pGia, pObj) );
        Vec_IntPush( vStack, Gia_ObjFaninId1p(pUnroll->pGia, pObj) );
    }
    Vec_IntSort( vNodes, 0 );
    Gia_ManConst0(pUnroll->pGia)->Value = 0;
    Vec_IntPush( vOrigin, 0 );
    Vec_IntForEachEntry( vNodes, Id, i )
    {
        if ( Id == 0 ) continue;
        pObj = Gia_ManObj( pUnroll->pGia, Id );
        pObj->Value = Vec_IntEntry(pUnroll->vVars, Id) >= 0 ? Gia_ManAppendCi(pChunk) :
            Gia_ManAppendAnd(pChunk, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj));
        Vec_IntPush( vOrigin, Id );
    }
    Vec_IntForEachEntry( vRoots, Lit, i )
    {
        Gia_ManAppendCo( pChunk, Gia_ManObj(pUnroll->pGia, Abc_Lit2Var(Lit))->Value ^ Abc_LitIsCompl(Lit) );
        Vec_IntPush( vOrigin, -1 );
    }
    pAig = Gia_ManToAigSimple( pChunk );
    pCnf = Cnf_Derive( pAig, Aig_ManCoNum(pAig) );
    vMap = Vec_IntStartFull( pCnf->nVars );
    vSkip = Vec_StrStart( pCnf->nVars );
    // The fresh chunk's constant-one variable aliases the old constant.
    Var = pCnf->pVarNums[Aig_ManConst1(pAig)->Id];
    Vec_IntWriteEntry( vMap, Var, 1 );
    Vec_StrWriteEntry( vSkip, Var, 1 );
    Gia_ManForEachCi( pChunk, pObj, i )
    {
        Id = Vec_IntEntry( vOrigin, Gia_ObjId(pChunk, pObj) );
        Var = pCnf->pVarNums[Abc_Lit2Var(pObj->Value)];
        Vec_IntWriteEntry( vMap, Var, Vec_IntEntry(pUnroll->vVars, Id) ^ Abc_LitIsCompl(pObj->Value) );
    }
    for ( i = 0; i < pCnf->nVars; i++ )
        if ( Vec_IntEntry(vMap, i) < 0 )
            Vec_IntWriteEntry( vMap, i, Abc_Var2Lit(pUnroll->nVars++, 0) );
    Gia_ManForEachAnd( pChunk, pObj, i )
    {
        Var = pCnf->pVarNums[Abc_Lit2Var(pObj->Value)];
        if ( Var >= 0 )
            Vec_IntWriteEntry( pUnroll->vVars, Vec_IntEntry(vOrigin, Gia_ObjId(pChunk, pObj)),
                Vec_IntEntry(vMap, Var) ^ Abc_LitIsCompl(pObj->Value) );
    }
    vResult = Vec_IntAlloc( Vec_IntSize(vRoots) );
    Gia_ManForEachCo( pChunk, pObj, i )
    {
        Var = pCnf->pVarNums[Abc_Lit2Var(pObj->Value)];
        Lit = Vec_IntEntry( vMap, Var ) ^ Abc_LitIsCompl(pObj->Value);
        assert( !Abc_LitIsCompl(Lit) );
        Vec_IntPush( vResult, Abc_Lit2Var(Lit) );
        Out = Vec_IntEntry( vRoots, i );
        if ( Vec_IntEntry(pUnroll->vVars, Abc_Lit2Var(Out)) < 0 )
            Vec_IntWriteEntry( pUnroll->vVars, Abc_Lit2Var(Out), Lit ^ Abc_LitIsCompl(Out) );
    }
    for ( i = 0; i < pCnf->nClauses; i++ )
        if ( !Vec_StrEntry(vSkip, Abc_Lit2Var(pCnf->pClauses[i][0])) )
        {
            nClauses++;
            nLits += pCnf->pClauses[i+1] - pCnf->pClauses[i];
        }
    pNext = Cnf_DataAlloc( NULL, pUnroll->nVars, pOld->nClauses + nClauses, pOld->nLiterals + nLits );
    memcpy( pNext->pClauses[0], pOld->pClauses[0], sizeof(int) * pOld->nLiterals );
    for ( i = 1; i <= pOld->nClauses; i++ )
        pNext->pClauses[i] = pNext->pClauses[0] + (pOld->pClauses[i] - pOld->pClauses[0]);
    Offset = pOld->nLiterals;
    k = pOld->nClauses;
    Vec_IntFillExtra( p->vCnfStartB, pUnroll->nVars, -1 );
    Vec_IntFillExtra( p->vCnfCountB, pUnroll->nVars, 0 );
    for ( i = 0; i < pCnf->nClauses; i++ )
    {
        if ( Vec_StrEntry(vSkip, Abc_Lit2Var(pCnf->pClauses[i][0])) ) continue;
        Var = Abc_Lit2Var(Vec_IntEntry(vMap, Abc_Lit2Var(pCnf->pClauses[i][0])));
        if ( Vec_IntEntry(p->vCnfStartB, Var) < 0 ) Vec_IntWriteEntry( p->vCnfStartB, Var, k );
        assert( Vec_IntEntry(p->vCnfStartB, Var) + Vec_IntEntry(p->vCnfCountB, Var) == k );
        Vec_IntAddToEntry( p->vCnfCountB, Var, 1 );
        pNext->pClauses[k++] = pNext->pClauses[0] + Offset;
        for ( pLit = pCnf->pClauses[i]; pLit < pCnf->pClauses[i+1]; pLit++ )
            pNext->pClauses[0][Offset++] = Vec_IntEntry(vMap, Abc_Lit2Var(*pLit)) ^ Abc_LitIsCompl(*pLit);
    }
    assert( k == pNext->nClauses && Offset == pNext->nLiterals );
    p->pCnfB = pNext;
    Cnf_DataFree( pOld );
finish:
    Vec_IntFree( vStack );
    Vec_IntFree( vNodes );
    Vec_IntFree( vOrigin );
    Vec_IntFreeP( &vMap );
    Vec_StrFree( vSeen );
    Vec_StrFreeP( &vSkip );
    if ( pCnf ) Cnf_DataFree( pCnf );
    if ( pAig ) Aig_ManStop( pAig );
    Gia_ManStop( pChunk );
    return vResult;
}

/**Function*************************************************************

  Synopsis    [Extends a bounded prefix or suffix without remapping old cones.]

  Description [Mapped definitions retain their SAT variables across depths.
  New chunks treat old definitions as inputs and append only new clauses.
  Changing the boundary still starts a new image solver and proof object.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Imc_ManExtendSuffix( Imc_Man_t * p, int nFrames )
{
    Imc_Unr_t * pUnroll;
    Gia_Obj_t * pObj;
    Vec_Int_t * vRoots, * vOutputs;
    Vec_Str_t * vUsed;
    int i, Lit, Var, Reset, nOldFrames, nOldClauses, nOldInputs, nOldResets, * pLit;
    abctime Start = Abc_Clock();
    Imc_ManImageStop( p );
    p->nImageCalls = 0;
    if ( p->pUnroll && p->pUnroll->nFrames > nFrames ) Imc_ManUnrollStop( p );
    if ( p->pUnroll == NULL ) p->pUnroll = Imc_UnrStart( p );
    pUnroll = p->pUnroll;
    nOldFrames = pUnroll->nFrames;
    nOldClauses = p->pCnfB->nClauses;
    while ( pUnroll->nFrames < nFrames )
    {
        if ( p->TimeStop && Abc_Clock() >= p->TimeStop ) return 0;
        nOldInputs = Vec_IntSize( pUnroll->vInputs );
        nOldResets = Vec_IntSize( pUnroll->vResets );
        Gia_ManConst0(p->pGia)->Value = 0;
        Gia_ManForEachPi( p->pGia, pObj, i )
        {
            Lit = Imc_UnrInput( pUnroll );
            Vec_IntPush( pUnroll->vInputs, Abc_Lit2Var(Lit) );
            pObj->Value = Lit;
        }
        Reset = 0;
        if ( p->pPars->fBackward )
        {
            Reset = Imc_UnrInput( pUnroll );
            Vec_IntPush( pUnroll->vResets, Abc_Lit2Var(Reset) );
        }
        Gia_ManForEachRo( p->pGia, pObj, i )
            pObj->Value = Vec_IntEntry( pUnroll->vState, i );
        Gia_ManForEachAnd( p->pGia, pObj, i )
        {
            if ( (i & 1023) == 0 && p->TimeStop && Abc_Clock() >= p->TimeStop )
            {
                Vec_IntShrink( pUnroll->vInputs, nOldInputs );
                Vec_IntShrink( pUnroll->vResets, nOldResets );
                return 0;
            }
            pObj->Value = Gia_ManHashAnd( pUnroll->pGia, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        }
        if ( !p->pPars->fBackward )
        {
            Lit = Gia_ObjFanin0Copy( Gia_ManPo(p->pGia, 0) );
            Vec_IntPush( pUnroll->vBad, Lit );
            pUnroll->iFail = Gia_ManHashOr( pUnroll->pGia, pUnroll->iFail, Lit );
        }
        Gia_ManForEachRi( p->pGia, pObj, i )
            Vec_IntWriteEntry( pUnroll->vState, i, Gia_ManHashAnd(pUnroll->pGia, Gia_ObjFanin0Copy(pObj), Reset ^ 1) );
        pUnroll->nFrames++;
    }
    vRoots = Vec_IntAlloc( 32 );
    if ( p->pPars->fBackward ) Vec_IntAppend( vRoots, pUnroll->vState );
    else
    {
        Vec_IntPush( vRoots, pUnroll->iFail );
        Vec_IntAppend( vRoots, pUnroll->vBad );
    }
    vOutputs = Imc_UnrEncode( p, vRoots );
    Vec_IntFree( vRoots );
    if ( vOutputs == NULL ) return 0;
    Vec_IntFreeP( &p->vImagePis );
    Vec_IntFreeP( &p->vImageBad );
    Vec_IntFreeP( &p->vPrefix );
    Vec_IntFreeP( &p->vResets );
    p->vImagePis = Vec_IntAlloc( Vec_IntSize(pUnroll->vInputs) + Vec_IntSize(p->vPis) );
    if ( !p->pPars->fBackward ) Vec_IntAppend( p->vImagePis, p->vPis );
    Vec_IntForEachEntry( pUnroll->vInputs, Var, i )
        Vec_IntPush( p->vImagePis, p->pCnf->nVars + Abc_Lit2Var(Vec_IntEntry(pUnroll->vVars, Var)) );
    if ( p->pPars->fBackward )
    {
        p->vPrefix = vOutputs;
        p->vImageBad = Vec_IntStart( 1 );
        p->vResets = Vec_IntAlloc( Vec_IntSize(pUnroll->vResets) );
        Vec_IntForEachEntry( pUnroll->vResets, Var, i )
            Vec_IntPush( p->vResets, p->pCnf->nVars + Abc_Lit2Var(Vec_IntEntry(pUnroll->vVars, Var)) );
    }
    else
    {
        p->vImageBad = vOutputs;
        Vec_IntForEachEntry( vOutputs, Var, i )
            Vec_IntWriteEntry( vOutputs, i, Var + p->pCnf->nVars );
        Vec_IntFreeP( &p->vMapB );
        Vec_IntFreeP( &p->vSharedUsed );
        p->vMapB = Vec_IntAlloc( p->pCnfB->nVars );
        for ( i = 0; i < p->pCnfB->nVars; i++ ) Vec_IntPush( p->vMapB, p->pCnf->nVars + i );
        p->vPrefix = Vec_IntAlloc( Gia_ManRegNum(p->pGia) );
        p->vSharedUsed = Vec_IntAlloc( Gia_ManRegNum(p->pGia) );
        vUsed = Vec_StrStart( p->pCnfB->nVars );
        for ( pLit = p->pCnfB->pClauses[0]; pLit < p->pCnfB->pClauses[p->pCnfB->nClauses]; pLit++ )
            Vec_StrWriteEntry( vUsed, Abc_Lit2Var(*pLit), 1 );
        for ( i = 0; i < Gia_ManRegNum(p->pGia); i++ )
        {
            Var = Abc_Lit2Var(Vec_IntEntry(pUnroll->vVars, Gia_ObjId(pUnroll->pGia, Gia_ManCi(pUnroll->pGia, i))));
            Vec_IntPush( p->vPrefix, Var );
            Vec_IntWriteEntry( p->vMapB, Var, Vec_IntEntry(p->vRis, i) );
            if ( Vec_StrEntry(vUsed, Var) ) Vec_IntPush( p->vSharedUsed, i );
        }
        Vec_StrFree( vUsed );
    }
    if ( p->pPars->fVerbose )
        Abc_Print( 1, "IMC: Extended %s depth %d -> %d; clauses %d -> %d; CNF wall = %.6f s.\n",
            p->pPars->fBackward ? "prefix" : "suffix", nOldFrames, nFrames,
            nOldClauses, p->pCnfB->nClauses, (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC );
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
