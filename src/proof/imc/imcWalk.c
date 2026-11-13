/**CFile****************************************************************

  FileName    [imcWalk.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Interpolation-based model checking.]

  Synopsis    [SAT-guided concrete simulation of constrained transitions.]

  Author      [ABC contributors]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 23, 2026.]

  Revision    [$Id: imcWalk.c,v 1.00 2026/10/23 00:00:00 alanmi Exp $]

***********************************************************************/

#include "imcInt.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

// Mark the property conjunction once, including literal polarity.
/**Function*************************************************************

  Synopsis    [Marks the property conjunction with literal polarity.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Str_t * Imc_WalkSupport( Gia_Man_t * p, int Root )
{
    Vec_Str_t * vSeen = Vec_StrStart( 2 * Gia_ManObjNum(p) );
    Vec_Int_t * vStack = Vec_IntAlloc( 64 );
    Gia_Obj_t * pObj;
    int Lit;
    Vec_IntPush( vStack, Root );
    while ( Vec_IntSize(vStack) )
    {
        Lit = Vec_IntPop( vStack );
        if ( Vec_StrEntry(vSeen, Lit) )
            continue;
        Vec_StrWriteEntry( vSeen, Lit, 1 );
        pObj = Gia_ManObj( p, Abc_Lit2Var(Lit) );
        if ( Abc_LitIsCompl(Lit) || !Gia_ObjIsAnd(pObj) )
            continue;
        Vec_IntPush( vStack, Gia_ObjFaninLit0p(p, pObj) );
        Vec_IntPush( vStack, Gia_ObjFaninLit1p(p, pObj) );
    }
    Vec_IntFree( vStack );
    return vSeen;
}

/**Function*************************************************************

  Synopsis    [Checks whether a combinational cone contains a given leaf.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_WalkHasLeaf( Gia_Man_t * p, int Root, int Leaf )
{
    Vec_Int_t * vStack = Vec_IntAlloc( 64 );
    Gia_Obj_t * pObj;
    int Id, Result = 0;
    Gia_ManIncrementTravId( p );
    Vec_IntPush( vStack, Abc_Lit2Var(Root) );
    while ( Vec_IntSize(vStack) )
    {
        Id = Vec_IntPop( vStack );
        if ( Id == Abc_Lit2Var(Leaf) )
        {
            Result = 1;
            break;
        }
        pObj = Gia_ManObj( p, Id );
        if ( Gia_ObjIsTravIdCurrent(p, pObj) )
            continue;
        Gia_ObjSetTravIdCurrent( p, pObj );
        if ( !Gia_ObjIsAnd(pObj) )
            continue;
        Vec_IntPush( vStack, Gia_ObjFaninId0p(p, pObj) );
        Vec_IntPush( vStack, Gia_ObjFaninId1p(p, pObj) );
    }
    Vec_IntFree( vStack );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Checks the guided-simulation deadline.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_WalkStop( void * pData )
{
    return Imc_ManCheckStop(*(abctime *)pData);
}

/**Function*************************************************************

  Synopsis    [Advances the deterministic guided-simulation generator.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned Imc_WalkRandom( unsigned * pSeed )
{
    *pSeed ^= *pSeed << 13;
    *pSeed ^= *pSeed >> 17;
    *pSeed ^= *pSeed << 5;
    return *pSeed;
}

/**Function*************************************************************

  Synopsis    [Returns 1 only for a concrete, independently checked CEX.]

  Description [A single transition solver completes input patterns while
  keeping feedback predicates in the property's support enabled. This is
  useful when unconstrained simulation violates a relational encoding's
  validity monitor. UNSAT cores relax random input preferences. No result
  of this incomplete search can establish safety or restrict IMC proofs.]

  SideEffects [Stores a counterexample in pGia->pCexSeq.]

  SeeAlso     []

***********************************************************************/
int Imc_ManWalkCached( Gia_Man_t * pGia, Imc_Par_t * pPars, abctime TimeStart, abctime Budget, Aig_Man_t * pAig, Cnf_Dat_t * pCnf )
{
    int fOwn = pCnf == NULL;
    CCaDiCaL * pCad = NULL;
    Vec_Int_t * vFlags = Vec_IntAlloc( 8 ), * vSoft = Vec_IntAlloc( 32 );
    Vec_Str_t * vState = NULL, * vHistory = NULL, * vSupport = NULL;
    Vec_Wrd_t * vSeen = Vec_WrdAlloc( 128 );
    Gia_Obj_t * pObj;
    abctime TimeStop = Budget ? Abc_Clock() + Budget : 0;
    abctime TimeLimit = pPars->nTimeOut ? TimeStart + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC : 0;
    unsigned Seed = 12347, Pattern = 0;
    int nFrames = pPars->nFrameMax ? Abc_MinInt(127, pPars->nFrameMax) + 1 : 128;
    int nPis = Gia_ManPiNum(pGia), nRegs = Gia_ManRegNum(pGia);
    int i, k, f, w, Bad, iBadCo = 0, Var, Status, Leaf, nSteps = 0, Result = 0;
    int nStepMax = Budget ? 0 : Abc_MaxInt(16, Abc_MinInt(512, (1 << 22) / Gia_ManObjNum(pGia)));
    // Early walking on a logic-heavy transition needs enough work for
    // twice the frame bound in SAT attempts (up to four per frame).
    // The conflict cap still limits SAT work.
    if ( !Budget && nRegs && Gia_ManAndNum(pGia) / nRegs > 128 )
        nStepMax = Abc_MaxInt(nStepMax, 2 * nFrames);
    if ( TimeLimit && (!TimeStop || TimeLimit < TimeStop) ) TimeStop = TimeLimit;
    if ( nPis == 0 || nPis > 100000 || Gia_ManObjNum(pGia) > 2000000 || Imc_WalkStop(&TimeStop) )
        goto finish;
    Bad = Gia_ObjFaninLit0p( pGia, Gia_ManPo(pGia, 0) );
    pObj = Gia_ManObj( pGia, Abc_Lit2Var(Bad) );
    if ( Gia_ObjIsRo(pGia, pObj) && !Abc_LitIsCompl(Bad) )
    {
        iBadCo = Gia_ObjCioId(pObj) - nPis + 1;
        Bad = Gia_ObjFaninLit0p( pGia, Gia_ObjRoToRi(pGia, pObj) );
    }
    vSupport = Imc_WalkSupport( pGia, Bad );
    Gia_ManForEachRo( pGia, pObj, i )
    {
        int fPositive, fNegative;
        if ( (i & 63) == 0 && Imc_WalkStop(&TimeStop) )
            goto finish;
        Leaf = Gia_Obj2Lit( pGia, pObj );
        fNegative = Vec_StrEntry( vSupport, Leaf ^ 1 );
        fPositive = Vec_StrEntry( vSupport, Leaf );
        if ( !fPositive && !fNegative )
            continue;
        if ( !Imc_WalkHasLeaf(pGia, Gia_ObjFaninLit0p(pGia, Gia_ManRi(pGia, i)), Leaf) )
            continue;
        if ( fNegative )
            Vec_IntPush( vFlags, Abc_Var2Lit(i, 1) );
        if ( fPositive )
            Vec_IntPush( vFlags, Abc_Var2Lit(i, 0) );
    }
    if ( Vec_IntSize(vFlags) == 0 || Imc_WalkStop(&TimeStop) )
        goto finish;
    if ( fOwn )
    {
        pAig = Gia_ManToAigSimple( pGia );
        Aig_ManSetRegNum( pAig, 0 );
        pCnf = Cnf_Derive( pAig, Aig_ManCoNum(pAig) );
    }
    pCad = ccadical_init();
    ccadical_set_option( pCad, "quiet", 1 );
    ccadical_set_option( pCad, "congruence", 0 );
    ccadical_set_option( pCad, "inprocessing", 0 );
    ccadical_set_option( pCad, "phase", 0 );
    ccadical_set_terminate( pCad, &TimeStop, Imc_WalkStop );
    for ( i = 0; i < pCnf->nClauses; i++ )
    {
        int * pLit;
        for ( pLit = pCnf->pClauses[i]; pLit < pCnf->pClauses[i+1]; pLit++ )
            ccadical_add( pCad, (Abc_Lit2Var(*pLit) + 1) * (Abc_LitIsCompl(*pLit) ? -1 : 1) );
        ccadical_add( pCad, 0 );
    }
    // Validity flags guide only transitions that do not already hit bad.
    // A delayed property also needs the transition that triggers next bad.
    // Keep current bad as an escape so that its reporting frame is allowed.
    Vec_IntForEachEntry( vFlags, k, i )
    {
        Var = pCnf->pVarNums[Aig_ManCo(pAig, Abc_Lit2Var(k) + 1)->Id];
        ccadical_add( pCad, pCnf->pVarNums[Aig_ManCo(pAig, 0)->Id] + 1 );
        if ( iBadCo )
            ccadical_add( pCad, pCnf->pVarNums[Aig_ManCo(pAig, iBadCo)->Id] + 1 );
        ccadical_add( pCad, (Var + 1) * (Abc_LitIsCompl(k) ? -1 : 1) );
        ccadical_add( pCad, 0 );
    }
    vState = Vec_StrStart( nRegs );
    vHistory = Vec_StrStart( nFrames * nPis );
    for ( w = 0; w < 32 && !Imc_WalkStop(&TimeStop); w++ )
    {
        Vec_StrFill( vState, nRegs, 0 );
        Vec_WrdClear( vSeen );
        for ( f = 0; f < nFrames && !Imc_WalkStop(&TimeStop); f++ )
        {
            word Hash = ABC_CONST(0xcbf29ce484222325);
            int Attempt;
            // Repetition only ends this heuristic walk; it is not a proof.
            for ( i = 0; i < nRegs; i++ )
                Hash = (Hash ^ Vec_StrEntry(vState, i)) * ABC_CONST(0x100000001b3);
            if ( Vec_WrdFind(vSeen, Hash) >= 0 )
                break;
            Vec_WrdPush( vSeen, Hash );
            Vec_IntClear( vSoft );
            for ( i = 0; i < nPis; i++ )
            {
                if ( !(i & 31) )
                {
                    int Width = 1 << (Imc_WalkRandom(&Seed) & 3);
                    Pattern = Imc_WalkRandom(&Seed) & ((1u << Width) - 1);
                }
                Var = pCnf->pVarNums[Aig_ManCi(pAig, i)->Id];
                k = (Var + 1) * (((Pattern >> ((w & 1) ? 31 - (i & 31) : (i & 31))) & 1) ? 1 : -1);
                ccadical_phase( pCad, k );
                if ( i / 32 == w % ((nPis + 31) / 32) )
                    Vec_IntPush( vSoft, k );
            }
            Status = 0;
            for ( Attempt = 0; Attempt < 4 && !Imc_WalkStop(&TimeStop); Attempt++ )
            {
                int Count = 0, Limit = 2000;
                if ( nStepMax && (nSteps >= nStepMax || ccadical_conflicts(pCad) >= 4096) ) goto finish;
                if ( nStepMax ) Limit = Abc_MinInt(Limit, 4096 - ccadical_conflicts(pCad));
                if ( pPars->nConfLimit ) Limit = Abc_MinInt(Limit, pPars->nConfLimit);
                if ( Attempt == 3 )
                    Vec_IntClear( vSoft );
                for ( i = 0; i < nRegs; i++ )
                {
                    Var = pCnf->pVarNums[Aig_ManCi(pAig, nPis + i)->Id];
                    ccadical_assume( pCad, (Var + 1) * (Vec_StrEntry(vState, i) ? 1 : -1) );
                }
                Vec_IntForEachEntry( vSoft, k, i )
                    ccadical_assume( pCad, k );
                ccadical_limit( pCad, "conflicts", Limit );
                Status = ccadical_solve( pCad );
                nSteps++;
                if ( Status != 20 || Vec_IntSize(vSoft) == 0 )
                    break;
                Vec_IntForEachEntry( vSoft, k, i )
                    if ( !ccadical_failed(pCad, k) )
                        Vec_IntWriteEntry( vSoft, Count++, k );
                if ( Count == Vec_IntSize(vSoft) )
                    break;
                Vec_IntShrink( vSoft, Count );
            }
            if ( Status != 10 )
                break;
            for ( i = 0; i < nPis; i++ )
            {
                Var = pCnf->pVarNums[Aig_ManCi(pAig, i)->Id];
                Vec_StrWriteEntry( vHistory, f * nPis + i, ccadical_val(pCad, Var + 1) > 0 );
            }
            Var = pCnf->pVarNums[Aig_ManCo(pAig, 0)->Id];
            if ( ccadical_val(pCad, Var + 1) > 0 )
            {
                Abc_Cex_t * pCex = Abc_CexAlloc( nRegs, nPis, f + 1 );
                pCex->iPo = 0;
                pCex->iFrame = f;
                for ( i = 0; i < (f + 1) * nPis; i++ )
                    if ( Vec_StrEntry(vHistory, i) )
                        Imc_CexSetBit( pCex->pData, pCex->nRegs + i );
                if ( Gia_ManVerifyCex(pGia, pCex, 0) )
                {
                    pGia->pCexSeq = pCex;
                    pPars->iFrame = Abc_MaxInt( pPars->iFrame, f );
                    Result = 1;
                }
                else
                {
                    Abc_Print( -1, "IMC: SAT-guided counterexample verification failed.\n" );
                    Abc_CexFree( pCex );
                }
                goto finish;
            }
            for ( i = 0; i < nRegs; i++ )
            {
                Var = pCnf->pVarNums[Aig_ManCo(pAig, i + 1)->Id];
                Vec_StrWriteEntry( vState, i, ccadical_val(pCad, Var + 1) > 0 );
            }
        }
    }
finish:
    if ( pPars->fVerbose && nSteps )
        Abc_Print( 1, "IMC: SAT-guided simulation made %d SAT attempts%s.\n", nSteps, Result ? " and found a checked counterexample" : "" );
    Vec_StrFreeP( &vSupport );
    Vec_IntFree( vFlags );
    Vec_IntFree( vSoft );
    Vec_WrdFree( vSeen );
    Vec_StrFreeP( &vState );
    Vec_StrFreeP( &vHistory );
    if ( pCad )
        ccadical_release( pCad );
    if ( fOwn && pCnf )
        Cnf_DataFree( pCnf );
    if ( fOwn && pAig )
        Aig_ManStop( pAig );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Runs guided simulation with an internally owned transition encoding.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Imc_ManWalk( Gia_Man_t * pGia, Imc_Par_t * pPars, abctime TimeStart, abctime Budget )
{
    return Imc_ManWalkCached( pGia, pPars, TimeStart, Budget, NULL, NULL );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
