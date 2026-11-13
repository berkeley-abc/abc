/**CFile****************************************************************

  FileName    [imcHoud.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Interpolation-based model checking.]

  Synopsis    [Inductive filtering of guarded state predicates.]

  Author      [ABC contributors]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 23, 2026.]

  Revision    [$Id: imcHoud.c,v 1.00 2026/10/23 00:00:00 alanmi Exp $]

***********************************************************************/

#include "imcInt.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Imc_Hou_t_ Imc_Hou_t;
struct Imc_Hou_t_
{
    CCaDiCaL * pSat;
    int nVars;
    int Zero;
    int nConfLimit;
    int nConfMax;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Converts an ABC literal to CaDiCaL's signed literal format.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_HouSigned( int Lit )
{
    return (Abc_Lit2Var(Lit) + 1) * (Abc_LitIsCompl(Lit) ? -1 : 1);
}

// The early induction attempt has a total conflict budget. Full attempts
// retain the caller's per-query limits and global deadline.
/**Function*************************************************************

  Synopsis    [Solves a Houdini query within its per-query and total conflict limits.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_HouSolve( Imc_Hou_t * p, int Limit )
{
    if ( p->nConfLimit ) Limit = Abc_MinInt(Limit, p->nConfLimit);
    if ( p->nConfMax )
    {
        int Remaining = p->nConfMax - ccadical_conflicts(p->pSat);
        if ( Remaining <= 0 ) return 0;
        Limit = Abc_MinInt( Limit, Remaining );
    }
    ccadical_limit( p->pSat, "conflicts", Limit );
    return ccadical_solve( p->pSat );
}

/**Function*************************************************************

  Synopsis    [Adds an ABC-literal clause to the Houdini solver.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_HouClause( Imc_Hou_t * p, int * pLits, int nLits )
{
    int i;
    for ( i = 0; i < nLits; i++ )
        ccadical_add( p->pSat, Imc_HouSigned(pLits[i]) );
    ccadical_add( p->pSat, 0 );
}

/**Function*************************************************************

  Synopsis    [Encodes a conjunction and returns its ABC literal.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_HouAnd( Imc_Hou_t * p, int a, int b )
{
    int Lit = Abc_Var2Lit( p->nVars++, 0 ), Lits[3];
    Lits[0] = Lit ^ 1; Lits[1] = a;
    Imc_HouClause( p, Lits, 2 );
    Lits[1] = b;
    Imc_HouClause( p, Lits, 2 );
    Lits[0] = Lit; Lits[1] = a ^ 1; Lits[2] = b ^ 1;
    Imc_HouClause( p, Lits, 3 );
    return Lit;
}

/**Function*************************************************************

  Synopsis    [Reads the model value of an ABC literal.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_HouValue( Imc_Hou_t * p, int Lit )
{
    return (ccadical_val(p->pSat, Abc_Lit2Var(Lit) + 1) > 0) ^ Abc_LitIsCompl(Lit);
}

/**Function*************************************************************

  Synopsis    [Checks the deadline of the Houdini solver.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_HouStop( void * pUser )
{
    abctime TimeStop = *(abctime *)pUser;
    return Imc_ManCheckStop(TimeStop);
}

/**Function*************************************************************

  Synopsis    [Encodes predicate outputs for the supplied input literals.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Imc_HouEncode( Imc_Hou_t * p, Gia_Man_t * pPred, Vec_Int_t * vInputs, abctime TimeStop )
{
    Vec_Int_t * vResult = Vec_IntAlloc( Gia_ManCoNum(pPred) );
    Gia_Obj_t * pObj;
    int i;
    Gia_ManConst0(pPred)->Value = p->Zero;
    Gia_ManForEachCi( pPred, pObj, i )
        pObj->Value = Abc_Var2Lit( Vec_IntEntry(vInputs, i), 0 );
    Gia_ManForEachAnd( pPred, pObj, i )
    {
        if ( (i & 1023) == 0 && Imc_HouStop(&TimeStop) )
        {
            Vec_IntFree( vResult );
            return NULL;
        }
        pObj->Value = Imc_HouAnd( p, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    }
    Gia_ManForEachCo( pPred, pObj, i )
        Vec_IntPush( vResult, Gia_ObjFanin0Copy(pObj) );
    return vResult;
}

/**Function*************************************************************

  Synopsis    [Builds the conjunction of the active guarded predicate templates.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Imc_HouInvariant( Gia_Man_t * pPred, Vec_Int_t * vGuards, Vec_Int_t * vTerms, Vec_Str_t * vActive )
{
    Gia_Man_t * pNew = Gia_ManStart( Gia_ManObjNum(pPred) + 4 * Vec_IntSize(vTerms) ), * pResult;
    Gia_Obj_t * pObj;
    int i, Guard, Term, Lit, Root = 1;
    Gia_ManHashStart( pNew );
    Gia_ManConst0(pPred)->Value = 0;
    Gia_ManForEachCi( pPred, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( pPred, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Vec_IntForEachEntry( vTerms, Term, i )
    {
        if ( !Vec_StrEntry(vActive, i) )
            continue;
        Guard = Vec_IntEntry( vGuards, i );
        Lit = Gia_ObjFanin0Copy( Gia_ManCo(pPred, Abc_Lit2Var(Term)) ) ^ Abc_LitIsCompl(Term);
        if ( Guard >= 0 )
            Lit = Gia_ManHashOr( pNew, Lit, Gia_ObjFanin0Copy(Gia_ManCo(pPred, Abc_Lit2Var(Guard))) ^ Abc_LitIsCompl(Guard) ^ 1 );
        Root = Gia_ManHashAnd( pNew, Root, Lit );
    }
    Gia_ManAppendCo( pNew, Root );
    Gia_ManHashStop( pNew );
    pResult = Gia_ManCleanup( pNew );
    Gia_ManStop( pNew );
    return pResult;
}

/**Function*************************************************************

  Synopsis    [Adds a distinct nonconstant guard within the guard limit.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_HouAddGuard( Gia_Man_t * p, Vec_Int_t * vGuards, int Lit )
{
    Gia_Obj_t * pObj;
    int i;
    if ( Lit < 2 || Vec_IntSize(vGuards) >= 64 )
        return;
    Gia_ManForEachCo( p, pObj, i )
        if ( Abc_Lit2Var(Gia_ObjFaninLit0p(p, pObj)) == Abc_Lit2Var(Lit) )
        {
            Vec_IntPushUnique( vGuards, Abc_Var2Lit(i, (Gia_ObjFaninLit0p(p, pObj) ^ Lit) & 1) );
            return;
        }
    Vec_IntPush( vGuards, Abc_Var2Lit(Gia_ManCoNum(p), 0) );
    Gia_ManAppendCo( p, Lit );
}

/**Function*************************************************************

  Synopsis    [Collects control guards from predicate outputs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_HouControlGuards( Gia_Man_t * pPred, Gia_Man_t * pNew, Vec_Int_t * vGuards, int Base )
{
    Vec_Int_t * vStack = Vec_IntAlloc( 32 );
    Vec_Str_t * vSeen = Vec_StrStart( Gia_ManObjNum(pPred) );
    Vec_Wrd_t * vMasks = Vec_WrdStart( Gia_ManObjNum(pPred) );
    Gia_Obj_t * pObj;
    int i, Id, Pol, Count, nControls = 0;
    word Mask, Outside = (word)1 << 63;
    Vec_IntPush( vStack, Gia_ObjFaninId0p(pPred, Gia_ManCo(pPred, Gia_ManCoNum(pPred) - 1)) );
    while ( Vec_IntSize(vStack) )
    {
        Id = Vec_IntPop( vStack );
        pObj = Gia_ManObj( pPred, Id );
        if ( Vec_StrEntry(vSeen, Id) )
            continue;
        Vec_StrWriteEntry( vSeen, Id, 1 );
        if ( Gia_ObjIsCi(pObj) )
        {
            if ( nControls == 16 )
                goto finish;
            Vec_WrdWriteEntry( vMasks, Id, (word)1 << nControls++ );
        }
        else if ( Gia_ObjIsAnd(pObj) )
        {
            Vec_IntPush( vStack, Gia_ObjFaninId0p(pPred, pObj) );
            Vec_IntPush( vStack, Gia_ObjFaninId1p(pPred, pObj) );
        }
    }
    Gia_ManForEachCi( pPred, pObj, i )
        if ( Vec_WrdEntry(vMasks, Gia_ObjId(pPred, pObj)) == 0 )
            Vec_WrdWriteEntry( vMasks, Gia_ObjId(pPred, pObj), Outside );
    Gia_ManForEachAnd( pPred, pObj, i )
        Vec_WrdWriteEntry( vMasks, i, Vec_WrdEntry(vMasks, Gia_ObjFaninId0p(pPred, pObj)) | Vec_WrdEntry(vMasks, Gia_ObjFaninId1p(pPred, pObj)) );
    Gia_ManForEachCo( pPred, pObj, i )
    {
        Mask = Vec_WrdEntry( vMasks, Gia_ObjFaninId0p(pPred, pObj) );
        if ( Mask & Outside )
            continue;
        for ( Count = 0; Mask; Count++ )
            Mask &= Mask - 1;
        if ( Count < 2 || Count > 4 )
            continue;
        for ( Pol = 0; Pol < 2; Pol++ )
            Imc_HouAddGuard( pNew, vGuards, Gia_ManHashAnd(pNew, Base, Gia_ObjFaninLit0p(pNew, Gia_ManCo(pNew, i)) ^ Pol) );
    }
finish:
    Vec_IntFree( vStack );
    Vec_StrFree( vSeen );
    Vec_WrdFree( vMasks );
}

/**Function*************************************************************

  Synopsis    [Builds the guard network for predicate induction.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Imc_HouGuards( Gia_Man_t * pPred, Gia_Man_t * pGia, Vec_Int_t * vGuards )
{
    Gia_Man_t * pNew = Gia_ManDup( pPred );
    Vec_Int_t * vControls = Vec_IntAlloc( 4 );
    Gia_Obj_t * pObj;
    int i, j, k, Reg, Lit, Base = Gia_ObjFaninLit0p(pNew, Gia_ManCo(pNew, Gia_ManCoNum(pNew) - 2));
    int nPreds = Gia_ManCoNum(pPred);
    // Equality with a register having a constant successor exposes a
    // saved initialization flag. Its value distinguishes recording before
    // initialization from recording later in the reachable computation.
    Gia_ManForEachCo( pPred, pObj, i )
    {
        Gia_Obj_t * p0, * p1;
        int a, b;
        if ( !Gia_ObjRecognizeExor(Gia_ObjFanin0(pObj), &p0, &p1) )
            continue;
        p0 = Gia_Regular(p0); p1 = Gia_Regular(p1);
        if ( !Gia_ObjIsCi(p0) || !Gia_ObjIsCi(p1) )
            continue;
        a = Gia_ObjCioId(p0); b = Gia_ObjCioId(p1);
        if ( Gia_ObjIsConst0(Gia_ObjFanin0(Gia_ManRi(pGia, a))) )
            Vec_IntPushUnique( vControls, b );
        if ( Gia_ObjIsConst0(Gia_ObjFanin0(Gia_ManRi(pGia, b))) )
            Vec_IntPushUnique( vControls, a );
    }
    Vec_IntPush( vGuards, -1 );
    Vec_IntPush( vGuards, Abc_Var2Lit(nPreds - 2, 0) );
    Vec_IntPush( vGuards, Abc_Var2Lit(nPreds - 1, 0) );
    Gia_ManHashStart( pNew );
    Gia_ManForEachCo( pPred, pObj, i )
    {
        Gia_Obj_t * pInput = Gia_ObjFanin0( pObj );
        Gia_Obj_t * pRo, * pDriver;
        if ( !Gia_ObjIsCi(pInput) || Vec_IntSize(vGuards) >= 64 )
            continue;
        pRo = Gia_ManRo( pGia, Gia_ObjCioId(pInput) );
        pDriver = Gia_ObjFanin0( Gia_ObjRoToRi(pGia, pRo) );
        if ( pDriver != pRo && !Gia_ObjIsConst0(pDriver) &&
             (!Gia_ObjIsAnd(pDriver) || (Gia_ObjFanin0(pDriver) != pRo && Gia_ObjFanin1(pDriver) != pRo)) )
            continue;
        for ( k = 0; k < 2; k++ )
        {
            if ( Vec_IntSize(vGuards) < 64 )
                Vec_IntPushUnique( vGuards, Abc_Var2Lit(i, k) );
            Lit = Gia_ManHashAnd( pNew, Base, Gia_ObjFaninLit0p(pNew, Gia_ManCo(pNew, i)) ^ k );
            Imc_HouAddGuard( pNew, vGuards, Lit );
        }
        if ( Vec_IntSize(vControls) <= 4 )
            Vec_IntForEachEntry( vControls, Reg, j )
                for ( k = 0; k < 2; k++ )
                {
                    Lit = Gia_ManHashAnd( pNew, Base, Gia_ObjFaninLit0p(pNew, Gia_ManCo(pNew, i)) );
                    Lit = Gia_ManHashAnd( pNew, Lit, Gia_Obj2Lit(pNew, Gia_ManCi(pNew, Reg)) ^ k );
                    Imc_HouAddGuard( pNew, vGuards, Lit );
                }
    }
    Imc_HouControlGuards( pPred, pNew, vGuards, Base );
    Gia_ManHashStop( pNew );
    Vec_IntFree( vControls );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Reads a possibly complemented simulation word.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static word Imc_HouSimLit( word * pValues, int Lit )
{
    return pValues[Abc_Lit2Var(Lit)] ^ (Abc_LitIsCompl(Lit) ? ~(word)0 : 0);
}

// Simulation only discards candidate conjuncts. The surviving conjunction
// still needs the complete induction check and the independent AIG check.
/**Function*************************************************************

  Synopsis    [Rejects candidate templates using concrete sequential simulation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Vec_Str_t * Imc_HouFilter( Gia_Man_t * pGia, Gia_Man_t * pPred, Vec_Int_t * vGuards, int nTerms, abctime TimeStop )
{
    Vec_Str_t * vReject = Vec_StrStart( 2 * nTerms * Vec_IntSize(vGuards) );
    word * pValues = ABC_CALLOC( word, Gia_ManObjNum(pGia) );
    word * pPredValues = ABC_CALLOC( word, Gia_ManObjNum(pPred) );
    word Seed = ABC_CONST(0x6a09e667f3bcc909), GuardValue, TermValue;
    Gia_Obj_t * pObj;
    int i, k, f, Mode, Guard;
    int nFrames = Abc_MaxInt( 8, Abc_MinInt(256, (1 << 22) /
        (Gia_ManObjNum(pGia) + 2 * nTerms * Vec_IntSize(vGuards))) );
    for ( Mode = 0; Mode < 3; Mode++ )
    {
        memset( pValues, 0, sizeof(word) * Gia_ManObjNum(pGia) );
        for ( f = 0; f < nFrames && (!Imc_ManCheckStop(TimeStop)); f++ )
        {
            Gia_ManForEachPi( pGia, pObj, i )
                pValues[Gia_ObjId(pGia, pObj)] = Imc_ManSimInput( i, f, Mode == 1 ? 4 : Mode == 2 ? 1 : 0, &Seed );
            Gia_ManForEachAnd( pGia, pObj, i )
                pValues[i] = Imc_HouSimLit(pValues, Gia_ObjFaninLit0p(pGia, pObj)) &
                             Imc_HouSimLit(pValues, Gia_ObjFaninLit1p(pGia, pObj));
            Gia_ManForEachCo( pGia, pObj, i )
                pValues[Gia_ObjId(pGia, pObj)] = Imc_HouSimLit(pValues, Gia_ObjFaninLit0p(pGia, pObj));
            Gia_ManForEachCi( pPred, pObj, i )
                pPredValues[Gia_ObjId(pPred, pObj)] = pValues[Gia_ObjId(pGia, Gia_ManRo(pGia, i))];
            Gia_ManForEachAnd( pPred, pObj, i )
                pPredValues[i] = Imc_HouSimLit(pPredValues, Gia_ObjFaninLit0p(pPred, pObj)) &
                                 Imc_HouSimLit(pPredValues, Gia_ObjFaninLit1p(pPred, pObj));
            Vec_IntForEachEntry( vGuards, Guard, k )
            {
                GuardValue = Guard < 0 ? ~(word)0 : Imc_HouSimLit(pPredValues,
                    Gia_ObjFaninLit0p(pPred, Gia_ManCo(pPred, Abc_Lit2Var(Guard))) ^ Abc_LitIsCompl(Guard));
                if ( !GuardValue )
                    continue;
                for ( i = 0; i < nTerms; i++ )
                {
                    TermValue = Imc_HouSimLit(pPredValues, Gia_ObjFaninLit0p(pPred, Gia_ManCo(pPred, i)));
                    if ( GuardValue & ~TermValue ) Vec_StrWriteEntry( vReject, 2 * (k * nTerms + i), 1 );
                    if ( GuardValue & TermValue ) Vec_StrWriteEntry( vReject, 2 * (k * nTerms + i) + 1, 1 );
                }
            }
            Gia_ManForEachRo( pGia, pObj, i )
                pValues[Gia_ObjId(pGia, pObj)] = pValues[Gia_ObjId(pGia, Gia_ManRi(pGia, i))];
        }
    }
    ABC_FREE( pValues );
    ABC_FREE( pPredValues );
    return vReject;
}

// Close the safety core under inductive dependencies. Every added term
// is justified by an UNSAT core, and the final smaller invariant is
// checked independently by the caller on the original circuit.
/**Function*************************************************************

  Synopsis    [Removes active templates outside the safety and induction cores.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_HouMinimize( Imc_Hou_t * p, Vec_Int_t * vNext, Vec_Int_t * vGuards,
    Vec_Int_t * vTerms, Vec_Int_t * vActs, Vec_Str_t * vActive, abctime TimeStop )
{
    Vec_Str_t * vNeeded = Vec_StrStart( Vec_IntSize(vTerms) );
    int i, Round, Guard, Term, Act, Fail, Violation, Added, nKept = 0;
    Vec_IntForEachEntry( vActs, Act, i )
        if ( Vec_StrEntry(vActive, i) && ccadical_failed(p->pSat, Imc_HouSigned(Act)) )
            Vec_StrWriteEntry( vNeeded, i, 1 );
    for ( Round = 0; Round < 16 && !Imc_HouStop(&TimeStop); Round++ )
    {
        Fail = p->Zero;
        Vec_IntForEachEntry( vTerms, Term, i )
        {
            if ( !Vec_StrEntry(vNeeded, i) )
                continue;
            Guard = Vec_IntEntry( vGuards, i );
            Violation = Vec_IntEntry(vNext, Abc_Lit2Var(Term)) ^ Abc_LitIsCompl(Term) ^ 1;
            if ( Guard >= 0 )
                Violation = Imc_HouAnd( p, Violation, Vec_IntEntry(vNext, Abc_Lit2Var(Guard)) ^ Abc_LitIsCompl(Guard) );
            Fail = Imc_HouAnd( p, Fail ^ 1, Violation ^ 1 ) ^ 1;
        }
        Vec_IntForEachEntry( vActs, Act, i )
            if ( Vec_StrEntry(vActive, i) )
                ccadical_assume( p->pSat, Imc_HouSigned(Act) );
        ccadical_assume( p->pSat, Imc_HouSigned(Fail) );
        if ( Imc_HouSolve( p, 20000 ) != 20 )
            break;
        Added = 0;
        Vec_IntForEachEntry( vActs, Act, i )
            if ( Vec_StrEntry(vActive, i) && !Vec_StrEntry(vNeeded, i) && ccadical_failed(p->pSat, Imc_HouSigned(Act)) )
            {
                Vec_StrWriteEntry( vNeeded, i, 1 );
                Added++;
            }
        if ( Added )
            continue;
        for ( i = 0; i < Vec_StrSize(vActive); i++ )
            if ( Vec_StrEntry(vActive, i) && !Vec_StrEntry(vNeeded, i) )
            {
                int Lit = Vec_IntEntry(vActs, i) ^ 1;
                Vec_StrWriteEntry( vActive, i, 0 );
                Imc_HouClause( p, &Lit, 1 );
            }
        break;
    }
    for ( i = 0; i < Vec_StrSize(vActive); i++ )
        nKept += Vec_StrEntry( vActive, i );
    Vec_StrFree( vNeeded );
    return nKept;
}

// Complete concrete transitions under the validity guard when random
// inputs almost always disable a relational encoding. As with the word
// simulation filter, discarded candidates are not used in any proof.
/**Function*************************************************************

  Synopsis    [Filters templates using SAT-generated concrete transitions.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_HouFilterSat( Imc_Hou_t * p, Imc_Man_t * pMan, Vec_Int_t * vNext,
    Vec_Int_t * vGuards, Vec_Str_t * vReject, int nTerms, abctime TimeStop )
{
    Vec_Str_t * vState = Vec_StrStart( Gia_ManRegNum(pMan->pGia) );
    int i, k, f, Trace, Guard, Var, Lit, Status, Value;
    int nPis = Gia_ManPiNum(pMan->pGia);
    for ( Trace = 0; Trace < 8 && !Imc_HouStop(&TimeStop); Trace++ )
    {
        Vec_StrFill( vState, Vec_StrSize(vState), 0 );
        for ( f = 0; f < 128 && !Imc_HouStop(&TimeStop); f++ )
        {
            for ( i = 0; i < nPis; i++ )
            {
                unsigned Pattern = 1 + (unsigned)((Trace + 3 * (i / 32)) & 7);
                Var = pMan->pCnf->pVarNums[Aig_ManCi(pMan->pAig, i)->Id];
                Value = (Pattern >> ((Trace & 1) ? 31 - (i & 31) : (i & 31))) & 1;
                ccadical_phase( p->pSat, (Var + 1) * (Value ? 1 : -1) );
            }
            Vec_IntForEachEntry( pMan->vRos, Var, i )
                ccadical_assume( p->pSat, (Var + 1) * (Vec_StrEntry(vState, i) ? 1 : -1) );
            ccadical_assume( p->pSat, Imc_HouSigned(Vec_IntEntry(vNext, nTerms - 2)) );
            Status = Imc_HouSolve( p, 1000 );
            if ( Status != 10 )
                break;
            pMan->nHouSatFiltered++;
            Vec_IntForEachEntry( vGuards, Guard, k )
            {
                if ( Guard >= 0 && !Imc_HouValue(p, Vec_IntEntry(vNext, Abc_Lit2Var(Guard)) ^ Abc_LitIsCompl(Guard)) )
                    continue;
                for ( i = 0; i < nTerms; i++ )
                {
                    Lit = Vec_IntEntry( vNext, i );
                    Vec_StrWriteEntry( vReject, 2 * (k * nTerms + i) + Imc_HouValue(p, Lit), 1 );
                }
            }
            Vec_IntForEachEntry( pMan->vRis, Var, i )
                Vec_StrWriteEntry( vState, i, ccadical_val(p->pSat, Var + 1) > 0 );
        }
    }
    for ( i = 0; i < nPis; i++ )
    {
        Var = pMan->pCnf->pVarNums[Aig_ManCi(pMan->pAig, i)->Id];
        ccadical_unphase( p->pSat, Var + 1 );
    }
    Vec_StrFree( vState );
}

/**Function*************************************************************

  Synopsis    [Encodes one guarded template and its successor violation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_HouCandidate( Imc_Hou_t * p, Vec_Int_t * vCurrent, Vec_Int_t * vNext,
    Vec_Int_t * vGuards, Vec_Int_t * vTerms, Vec_Int_t * vActs, Vec_Str_t * vActive,
    int Guard, int Term, Vec_Int_t * vFails )
{
    int Act = Abc_Var2Lit( p->nVars++, 0 ), Lits[3], Violation;
    Vec_IntPush( vActs, Act );
    Vec_IntPush( vGuards, Guard );
    Vec_IntPush( vTerms, Term );
    Vec_StrPush( vActive, 1 );
    Lits[0] = Act ^ 1;
    Lits[1] = Vec_IntEntry(vCurrent, Abc_Lit2Var(Term)) ^ Abc_LitIsCompl(Term);
    if ( Guard >= 0 )
        Lits[2] = Vec_IntEntry(vCurrent, Abc_Lit2Var(Guard)) ^ Abc_LitIsCompl(Guard) ^ 1;
    Imc_HouClause( p, Lits, Guard < 0 ? 2 : 3 );
    Violation = Vec_IntEntry(vNext, Abc_Lit2Var(Term)) ^ Abc_LitIsCompl(Term) ^ 1;
    if ( Guard >= 0 )
        Violation = Imc_HouAnd( p, Violation, Vec_IntEntry(vNext, Abc_Lit2Var(Guard)) ^ Abc_LitIsCompl(Guard) );
    Violation = Imc_HouAnd( p, Violation, Act );
    Vec_IntPush( vFails, Violation );
}

// A positive selector requires one active violation. The reverse clauses
// are unnecessary: selectors occur only positively in assumptions, and
// disabling an old selector frees its clause after candidates are added.
/**Function*************************************************************

  Synopsis    [Builds the disjunction of violations of active candidates.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_HouFailure( Imc_Hou_t * p, Vec_Int_t * vFails, Vec_Str_t * vActive, int Old )
{
    int i, Lit, Fail = Abc_Var2Lit( p->nVars++, 0 );
    if ( Old != p->Zero )
    {
        Lit = Old ^ 1;
        Imc_HouClause( p, &Lit, 1 );
    }
    ccadical_add( p->pSat, Imc_HouSigned(Fail ^ 1) );
    Vec_IntForEachEntry( vFails, Lit, i )
        if ( Vec_StrEntry(vActive, i) )
            ccadical_add( p->pSat, Imc_HouSigned(Lit) );
    ccadical_add( p->pSat, 0 );
    return Fail;
}

// Seed a demand set with a safety core. Failed assumptions identify the
// candidate premises needed to exclude bad; no induction is claimed here.
/**Function*************************************************************

  Synopsis    [Extends the demanded premise set with a new safety core.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_HouSafetyCore( Imc_Hou_t * p, Vec_Int_t * vActs, Vec_Str_t * vActive,
    Vec_Str_t * vNeeded, Imc_Man_t * pMan )
{
    int i, Act;
    // Keep previously discovered induction premises that are still active.
    // A new safety core supplements this closure instead of erasing it.
    Vec_StrFillExtra( vNeeded, Vec_StrSize(vActive), 0 );
    for ( i = 0; i < Vec_StrSize(vActive); i++ )
        if ( !Vec_StrEntry(vActive, i) )
            Vec_StrWriteEntry( vNeeded, i, 0 );
        else if ( Vec_StrEntry(vNeeded, i) )
            pMan->nHouDemandRetained++;
    Vec_IntForEachEntry( vActs, Act, i )
        if ( Vec_StrEntry(vActive, i) )
            ccadical_assume( p->pSat, Imc_HouSigned(Act) );
    ccadical_assume( p->pSat, pMan->iBad + 1 );
    if ( Imc_HouSolve(p, 1024) != 20 ) return 0;
    Vec_IntForEachEntry( vActs, Act, i )
        if ( Vec_StrEntry(vActive, i) && ccadical_failed(p->pSat, Imc_HouSigned(Act)) )
            Vec_StrWriteEntry( vNeeded, i, 1 );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Returns an inductive restriction and tests whether it is safe.]

  Description [Houdini starts with predicate literals and implications
  guarded by at most 64 state conditions derived from the predicate outputs. Every candidate holds in
  the initial state. SAT models of F AND T AND NOT F' remove all falsified
  next-state candidates. An UNSAT result proves their conjunction
  inductive. A separate query checks that it excludes the bad output.
  The caller checks the returned AIG again using the independent solver.]

  SideEffects [Uses temporary predicate AIG values.]

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Imc_ManPredicateInvariant( Imc_Man_t * pMan, int * pfSafe )
{
    Imc_Hou_t Hou, * p = &Hou;
    Gia_Man_t * pPred = NULL, * pResult = NULL;
    Gia_Obj_t * pObj;
    Vec_Int_t * vInit = Vec_IntAlloc( Gia_ManCoNum(pMan->pPred) );
    Vec_Int_t * vCurrent = NULL, * vNext = NULL;
    Vec_Int_t * vGuards = Vec_IntAlloc( 512 ), * vTerms = Vec_IntAlloc( 512 ), * vActs = Vec_IntAlloc( 512 );
    Vec_Int_t * vGuardList = Vec_IntAlloc( 16 );
    Vec_Int_t * vBlocks = Vec_IntAlloc( 512 ), * vExpand = Vec_IntAlloc( 16 );
    Vec_Str_t * vNextValues = Vec_StrAlloc( 256 );
    Vec_Str_t * vActive = Vec_StrAlloc( 512 );
    Vec_Str_t * vNeeded = Vec_StrAlloc( 512 );
    Vec_Str_t * vReject = NULL, * vMade = NULL, * vBlocked = NULL;
    Vec_Int_t * vFails = Vec_IntAlloc( 512 ), * vVotes = NULL;
    Vec_Int_t * vCover = NULL, * vDropped = Vec_IntAlloc( 16 ), * vRetired = Vec_IntAlloc( 16 );
    // The caller reserves time for interpolation and other phases. Candidate,
    // transition and conflict limits bound this work without a second clock
    // budget that can discard nearly completed induction under machine load.
    abctime TimeStop = pMan->TimeStop, TimePhase = Abc_Clock();
    int i, k, Pol, Guard, Term, Act, Lits[3], Fail, Status, nTerms = Gia_ManCoNum(pMan->pPred), nLive = 0, nRounds = 0, nRemoved, nBefore, nFail, fInductive = 0, fDemand;
    memset( p, 0, sizeof(Imc_Hou_t) );
    p->nConfLimit = pMan->pPars->nConfLimit;
    p->nConfMax = pMan->nHouConfMax;
    pMan->nHouFiltered = pMan->nHouBlocked = pMan->nHouExpanded = pMan->nHouMinimized = 0;
    pMan->nHouSatFiltered = pMan->nHouCandidates = pMan->nHouCoreRemoved = 0;
    pMan->nHouDemandRefresh = pMan->nHouDemandRetained = pMan->nHouDemandFallback = pMan->nHouDemandExpanded = 0;
    *pfSafe = 0;
    if ( Imc_HouStop(&TimeStop) || nTerms < 2 || nTerms > IMC_PRED_MAX )
        goto finish;
    pPred = Imc_HouGuards( pMan->pPred, pMan->pGia, vGuardList );
    vCover = Vec_IntStartFull( 2 * nTerms );
    vMade = Vec_StrStart( 2 * nTerms * Vec_IntSize(vGuardList) );
    vBlocked = Vec_StrStart( Vec_IntSize(vGuardList) );
    Gia_ManConst0(pPred)->Value = 0;
    Gia_ManForEachCi( pPred, pObj, i )
        pObj->Value = 0;
    Gia_ManForEachAnd( pPred, pObj, i )
        pObj->Value = (Gia_ObjFanin0(pObj)->Value ^ Gia_ObjFaninC0(pObj)) &
                     (Gia_ObjFanin1(pObj)->Value ^ Gia_ObjFaninC1(pObj));
    Gia_ManForEachCo( pPred, pObj, i )
        Vec_IntPush( vInit, Gia_ObjFanin0(pObj)->Value ^ Gia_ObjFaninC0(pObj) );
    vReject = Imc_HouFilter( pMan->pGia, pPred, vGuardList, Gia_ManCoNum(pMan->pPred), TimeStop );
    if ( pMan->pPars->fVerbose )
        Abc_Print( 1, "IMC: Houdini simulation wall = %.6f s.\n", (double)(Abc_Clock() - TimePhase) / CLOCKS_PER_SEC );
    for ( i = 0; i < Vec_StrSize(vReject); i++ )
        pMan->nHouFiltered += Vec_StrEntry(vReject, i) != 0;
    p->pSat = ccadical_init();
    ccadical_set_option( p->pSat, "quiet", 1 );
    ccadical_set_option( p->pSat, "inprocessing", 0 );
    ccadical_set_option( p->pSat, "congruence", 0 );
    ccadical_set_terminate( p->pSat, &TimeStop, Imc_HouStop );
    p->nVars = pMan->pCnf->nVars;
    for ( i = 0; i < pMan->pCnf->nClauses; i++ )
    {
        if ( (i & 1023) == 0 && Imc_HouStop(&TimeStop) )
            goto finish;
        Imc_HouClause( p, pMan->pCnf->pClauses[i], pMan->pCnf->pClauses[i + 1] - pMan->pCnf->pClauses[i] );
    }
    p->Zero = Abc_Var2Lit( p->nVars++, 0 );
    Lits[0] = p->Zero ^ 1;
    Imc_HouClause( p, Lits, 1 );
    vCurrent = Imc_HouEncode( p, pPred, pMan->vRos, TimeStop );
    vNext = Imc_HouEncode( p, pPred, pMan->vRis, TimeStop );
    if ( vCurrent == NULL || vNext == NULL )
        goto finish;
    vVotes = Vec_IntStart( p->nVars );
    TimePhase = Abc_Clock();
    if ( vReject && Gia_ManPiNum(pMan->pGia) > Gia_ManRegNum(pMan->pGia) )
        Imc_HouFilterSat( p, pMan, vNext, vGuardList, vReject, Gia_ManCoNum(pMan->pPred), TimeStop );
    if ( pMan->pPars->fVerbose )
        Abc_Print( 1, "IMC: Houdini SAT filter wall = %.6f s; transitions = %d.\n",
            (double)(Abc_Clock() - TimePhase) / CLOCKS_PER_SEC, pMan->nHouSatFiltered );
    TimePhase = Abc_Clock();
    Fail = p->Zero;
    for ( k = 0; k < Vec_IntSize(vGuardList); k++ )
    {
        if ( Imc_HouStop(&TimeStop) )
            goto finish;
        if ( Vec_IntSize(vTerms) >= 16384 )
            break;
        Guard = Vec_IntEntry( vGuardList, k );
        if ( Guard >= 0 )
        {
            ccadical_assume( p->pSat, Imc_HouSigned(Vec_IntEntry(vCurrent, Abc_Lit2Var(Guard)) ^ Abc_LitIsCompl(Guard)) );
            if ( Imc_HouSolve( p, 200 ) == 20 )
            {
                Vec_StrWriteEntry( vBlocked, k, 2 );
                continue;
            }
        }
        // Until a guard is observed, all of its literal templates reduce
        // to NOT guard. Expand this group only if an induction model
        // reaches it, using that same model to discard false literals.
        if ( vReject && Guard >= 0 && !(Vec_IntEntry(vInit, Abc_Lit2Var(Guard)) ^ Abc_LitIsCompl(Guard)) )
        {
            for ( i = 0; i < 2 * Gia_ManCoNum(pMan->pPred); i++ )
                if ( Vec_StrEntry(vReject, 2 * k * Gia_ManCoNum(pMan->pPred) + i) )
                    break;
            if ( i == 2 * Gia_ManCoNum(pMan->pPred) )
            {
                Imc_HouCandidate( p, vCurrent, vNext, vGuards, vTerms, vActs, vActive, -1, Guard ^ 1, vFails );
                Vec_IntPush( vBlocks, k );
                Vec_StrWriteEntry( vBlocked, k, 1 );
                pMan->nHouBlocked++;
                continue;
            }
        }
        for ( i = 0; i < Gia_ManCoNum(pMan->pPred); i++ )
            for ( Pol = 0; Pol < 2; Pol++ )
            {
                if ( Imc_HouStop(&TimeStop) )
                    goto finish;
                if ( Vec_IntSize(vTerms) >= 16384 )
                    break;
                // An active T already implies every G -> T. Materialize
                // its guarded versions only after the unconditional T drops.
                if ( Guard >= 0 && Vec_IntEntry(vCover, 2 * i + Pol) >= 0 )
                    continue;
                if ( vReject && Vec_StrEntry(vReject, 2 * (k * Gia_ManCoNum(pMan->pPred) + i) + Pol) )
                    continue;
                if ( (Guard < 0 || (Vec_IntEntry(vInit, Abc_Lit2Var(Guard)) ^ Abc_LitIsCompl(Guard))) && !(Vec_IntEntry(vInit, i) ^ Pol) )
                    continue;
                if ( Guard < 0 )
                    Vec_IntWriteEntry( vCover, 2 * i + Pol, Vec_IntSize(vTerms) );
                Vec_StrWriteEntry( vMade, 2 * (k * nTerms + i) + Pol, 1 );
                Imc_HouCandidate( p, vCurrent, vNext, vGuards, vTerms, vActs, vActive, Guard, Abc_Var2Lit(i, Pol), vFails );
                Vec_IntPush( vBlocks, -1 );
            }
    }
    if ( pMan->pPars->fVerbose )
        Abc_Print( 1, "IMC: Houdini candidates wall = %.6f s.\n", (double)(Abc_Clock() - TimePhase) / CLOCKS_PER_SEC );
    TimePhase = Abc_Clock();
    nLive = Vec_IntSize( vTerms );
    nFail = nLive;
    // Recorded-state predicates benefit from a focused safety core. Keep
    // broad elimination for linear-word vocabularies, whose dependencies
    // often span most candidates. Small sets need no extra safety queries.
    fDemand = pMan->iPredClass != 2 && nLive >= 256 && Imc_HouSafetyCore( p, vActs, vActive, vNeeded, pMan );
    Fail = Imc_HouFailure( p, vFails, fDemand ? vNeeded : vActive, Fail );
    while ( !Imc_HouStop(&TimeStop) )
    {
        // Retired templates must not leave stale search preferences.
        Vec_IntForEachEntry( vNext, Term, i )
            ccadical_unphase( p->pSat, Abc_Lit2Var(Term) + 1 );
        // Choose one deterministic phase per variable by the number of
        // active templates it can help refute, rather than the last template
        // visited. These preferences never restrict the SAT query.
        Vec_IntFill( vVotes, Vec_IntSize(vVotes), 0 );
        Vec_IntForEachEntry( vTerms, Term, i )
            if ( Vec_StrEntry(vActive, i) )
            {
                int Lit;
                Guard = Vec_IntEntry( vGuards, i );
                if ( Guard >= 0 )
                {
                    Lit = Vec_IntEntry(vNext, Abc_Lit2Var(Guard)) ^ Abc_LitIsCompl(Guard);
                    Vec_IntAddToEntry( vVotes, Abc_Lit2Var(Lit), Abc_LitIsCompl(Lit) ? -1 : 1 );
                }
                Lit = Vec_IntEntry(vNext, Abc_Lit2Var(Term)) ^ Abc_LitIsCompl(Term) ^ 1;
                Vec_IntAddToEntry( vVotes, Abc_Lit2Var(Lit), Abc_LitIsCompl(Lit) ? -1 : 1 );
            }
        Vec_IntForEachEntry( vNext, Term, i )
        {
            int Var = Abc_Lit2Var(Term), Vote = Vec_IntEntry(vVotes, Var);
            if ( Vote ) ccadical_phase( p->pSat, Vote > 0 ? Var + 1 : -Var - 1 );
        }
        Vec_IntForEachEntry( vActs, Act, i )
            if ( Vec_StrEntry(vActive, i) )
                ccadical_assume( p->pSat, Imc_HouSigned(Act) );
        ccadical_assume( p->pSat, Imc_HouSigned(Fail) );
        Status = Imc_HouSolve( p, 20000 );
        nRounds++;
        if ( Status == 20 )
        {
            if ( fDemand )
            {
                // This query assumes all active premises but checks only
                // demanded successors. Close the demand set under its UNSAT
                // core before concluding that the smaller set is inductive.
                nRemoved = 0;
                Vec_IntForEachEntry( vActs, Act, i )
                    if ( Vec_StrEntry(vActive, i) && !Vec_StrEntry(vNeeded, i) &&
                         ccadical_failed(p->pSat, Imc_HouSigned(Act)) )
                    {
                        Vec_StrWriteEntry( vNeeded, i, 1 );
                        nRemoved++;
                    }
                if ( nRemoved )
                {
                    Fail = Imc_HouFailure( p, vFails, vNeeded, Fail );
                    continue;
                }
                Vec_IntForEachEntry( vActs, Act, i )
                    if ( Vec_StrEntry(vActive, i) && !Vec_StrEntry(vNeeded, i) )
                    {
                        Act ^= 1;
                        Vec_StrWriteEntry( vActive, i, 0 );
                        Imc_HouClause( p, &Act, 1 );
                        pMan->nHouCoreRemoved++;
                        nLive--;
                    }
                if ( pMan->pPars->fVerbose )
                    Abc_Print( 1, "IMC: Safety core closed with %d inductive templates.\n", nLive );
            }
            fInductive = 1;
            break;
        }
        if ( Status != 10 )
            goto finish;
        nRemoved = 0;
        Vec_IntClear( vExpand );
        Vec_IntClear( vDropped );
        Vec_IntClear( vRetired );
        Vec_IntForEachEntry( vTerms, Term, i )
        {
            if ( !Vec_StrEntry(vActive, i) )
                continue;
            Guard = Vec_IntEntry( vGuards, i );
            if ( (Guard < 0 || Imc_HouValue(p, Vec_IntEntry(vNext, Abc_Lit2Var(Guard)) ^ Abc_LitIsCompl(Guard))) &&
                 !Imc_HouValue(p, Vec_IntEntry(vNext, Abc_Lit2Var(Term)) ^ Abc_LitIsCompl(Term)) )
            {
                Vec_StrWriteEntry( vActive, i, 0 );
                Vec_IntPush( vRetired, Vec_IntEntry(vActs, i) ^ 1 );
                if ( Guard < 0 && Term < 2 * nTerms && Vec_IntEntry(vCover, Term) == i )
                {
                    Vec_IntWriteEntry( vCover, Term, -1 );
                    Vec_IntPush( vDropped, Term );
                }
                if ( Vec_IntEntry(vBlocks, i) >= 0 )
                    Vec_IntPush( vExpand, Vec_IntEntry(vBlocks, i) );
                nRemoved++;
            }
        }
        if ( nRemoved == 0 )
            goto finish;
        nLive -= nRemoved;
        // Adding the next failure formula invalidates CaDiCaL's SAT model.
        // Save expansion values before introducing any clauses or variables.
        if ( Vec_IntSize(vExpand) || Vec_IntSize(vDropped) )
        {
            Vec_StrClear( vNextValues );
            Vec_IntForEachEntry( vNext, Term, i )
                Vec_StrPush( vNextValues, Imc_HouValue(p, Term) );
        }
        Vec_IntForEachEntry( vRetired, Act, i )
            Imc_HouClause( p, &Act, 1 );
        nBefore = Vec_IntSize( vTerms );
        Vec_IntForEachEntry( vDropped, Term, i )
            for ( k = 1; k < Vec_IntSize(vGuardList); k++ )
            {
                int Key = 2 * k * nTerms + Term;
                if ( Imc_HouStop(&TimeStop) )
                    goto finish;
                if ( Vec_IntSize(vTerms) >= 16384 )
                    break;
                if ( Vec_StrEntry(vBlocked, k) || Vec_StrEntry(vMade, Key) || Vec_StrEntry(vReject, Key) )
                    continue;
                Guard = Vec_IntEntry( vGuardList, k );
                if ( (Vec_IntEntry(vInit, Abc_Lit2Var(Guard)) ^ Abc_LitIsCompl(Guard)) &&
                     !(Vec_IntEntry(vInit, Abc_Lit2Var(Term)) ^ Abc_LitIsCompl(Term)) )
                    continue;
                if ( (Vec_StrEntry(vNextValues, Abc_Lit2Var(Guard)) ^ Abc_LitIsCompl(Guard)) &&
                     !(Vec_StrEntry(vNextValues, Abc_Lit2Var(Term)) ^ Abc_LitIsCompl(Term)) )
                    continue;
                Vec_StrWriteEntry( vMade, Key, 1 );
                Imc_HouCandidate( p, vCurrent, vNext, vGuards, vTerms, vActs, vActive, Guard, Term, vFails );
                Vec_IntPush( vBlocks, -1 );
            }
        Vec_IntForEachEntry( vExpand, Guard, k )
        {
            int Group = Guard;
            pMan->nHouExpanded++;
            pMan->nHouDemandExpanded += fDemand;
            Vec_StrWriteEntry( vBlocked, Group, 0 );
            Guard = Vec_IntEntry( vGuardList, Group );
            for ( i = 0; i < Gia_ManCoNum(pMan->pPred); i++ )
            {
                if ( Imc_HouStop(&TimeStop) )
                    goto finish;
                if ( Vec_IntSize(vTerms) >= 16384 )
                    break;
                Pol = Vec_StrEntry( vNextValues, i ) ^ 1;
                if ( Vec_IntEntry(vCover, 2 * i + Pol) >= 0 || Vec_StrEntry(vMade, 2 * (Group * nTerms + i) + Pol) )
                    continue;
                Vec_StrWriteEntry( vMade, 2 * (Group * nTerms + i) + Pol, 1 );
                if ( Vec_StrEntry(vReject, 2 * (Group * Gia_ManCoNum(pMan->pPred) + i) + Pol) )
                    continue;
                Imc_HouCandidate( p, vCurrent, vNext, vGuards, vTerms, vActs, vActive, Guard, Abc_Var2Lit(i, Pol), vFails );
                Vec_IntPush( vBlocks, -1 );
            }
        }
        nLive += Vec_IntSize(vTerms) - nBefore;
        if ( fDemand )
        {
            // A demanded template was refuted. Refresh the safety core
            // after lazy guards are expanded. If safety no longer follows,
            // retain ordinary Houdini to discover a useful restriction.
            Vec_IntForEachEntry( vNext, Term, i )
                ccadical_unphase( p->pSat, Abc_Lit2Var(Term) + 1 );
            pMan->nHouDemandRefresh++;
            fDemand = Imc_HouSafetyCore( p, vActs, vActive, vNeeded, pMan );
            pMan->nHouDemandFallback += !fDemand;
            Fail = Imc_HouFailure( p, vFails, fDemand ? vNeeded : vActive, Fail );
            nFail = nLive;
        }
        else if ( Vec_IntSize(vTerms) > nBefore || nLive < nFail / 4 )
        {
            Fail = Imc_HouFailure( p, vFails, vActive, Fail );
            nFail = nLive;
        }
    }
    if ( pMan->pPars->fVerbose )
        Abc_Print( 1, "IMC: Houdini induction wall = %.6f s.\n", (double)(Abc_Clock() - TimePhase) / CLOCKS_PER_SEC );
    if ( !fInductive )
        goto finish;
    Vec_IntForEachEntry( vNext, Term, i )
        ccadical_unphase( p->pSat, Abc_Lit2Var(Term) + 1 );
    // A completed induction proof remains useful even if there is no
    // time left for safety. Return it with fSafe clear for caller checks.
    if ( !Imc_HouStop(&TimeStop) )
    {
        Vec_IntForEachEntry( vActs, Act, i )
            if ( Vec_StrEntry(vActive, i) )
                ccadical_assume( p->pSat, Imc_HouSigned(Act) );
        ccadical_assume( p->pSat, pMan->iBad + 1 );
        *pfSafe = Imc_HouSolve( p, 20000 ) == 20;
    }
    if ( *pfSafe )
    {
        TimePhase = Abc_Clock();
        nBefore = Vec_StrCountEntry( vActive, 1 );
        nLive = Imc_HouMinimize( p, vNext, vGuards, vTerms, vActs, vActive, TimeStop );
        pMan->nHouMinimized += nBefore - Vec_StrCountEntry( vActive, 1 );
        if ( pMan->pPars->fVerbose )
            Abc_Print( 1, "IMC: Houdini minimize wall = %.6f s.\n", (double)(Abc_Clock() - TimePhase) / CLOCKS_PER_SEC );
    }
    pResult = Imc_HouInvariant( pPred, vGuards, vTerms, vActive );
finish:
    pMan->nHouCandidates = Vec_IntSize(vTerms);
    if ( pMan->pPars->fVerbose && p->pSat )
        Abc_Print( 1, "IMC: Houdini conflicts = %d; minimized templates = %d; core removals = %d.\n",
            ccadical_conflicts(p->pSat), pMan->nHouMinimized, pMan->nHouCoreRemoved );
    if ( pMan->pPars->fVerbose )
        Abc_Print( 1, "IMC: Predicate induction retained %d of %d candidates in %d queries%s.\n",
            nLive, Vec_IntSize(vTerms), nRounds, *pfSafe ? " and excluded bad" : "" );
    if ( p->pSat )
        ccadical_release( p->pSat );
    Vec_IntFree( vInit );
    Vec_IntFreeP( &vCurrent );
    Vec_IntFreeP( &vNext );
    Vec_IntFree( vGuards );
    Vec_IntFree( vTerms );
    Vec_IntFree( vActs );
    Vec_IntFree( vGuardList );
    Vec_IntFree( vBlocks );
    Vec_IntFree( vExpand );
    Vec_StrFree( vNextValues );
    Vec_StrFree( vActive );
    Vec_StrFree( vNeeded );
    Vec_StrFreeP( &vReject );
    Vec_StrFreeP( &vMade );
    Vec_StrFreeP( &vBlocked );
    Vec_IntFreeP( &vCover );
    Vec_IntFree( vDropped );
    Vec_IntFree( vRetired );
    Vec_IntFree( vFails );
    Vec_IntFreeP( &vVotes );
    Gia_ManStopP( &pPred );
    return pResult;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
