/**CFile****************************************************************

  FileName    [imcPdr.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Interpolation-based model checking.]

  Synopsis    [Strengthens PDR frames with interpolants of bounded unrollings.]

  Description [Uses the clausal-trace and local strengthening ideas of
  Y. Vizel and A. Gurfinkel, Interpolating Property Directed Reachability,
  CAV 2014. Each proposed clause is checked on the concrete transition
  relation before PDR adds it to a frame.]

  Author      [ABC contributors]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 20, 2026.]

***********************************************************************/

#include "imcInt.h"
#include "aig/saig/saig.h"
#include "proof/pdr2/pdr2.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Imc_PdrItp_t_ Imc_PdrItp_t;
struct Imc_PdrItp_t_
{
    const Pdr2_Frame_t * pFrame;
    Imc_Par_t *  pPars;
    abctime      TimeStop;
    Vec_Wec_t *  vClauses;      // proof roots in insertion order
    Vec_Int_t *  vClauseFrame;  // partition owning each root
    Vec_Int_t *  vVarFrame;     // partition owning each private SAT variable
    Vec_Wec_t *  vStates;       // shared register literals at each time
    int          nFrameClauses;
    int          nCuts;
    int          fClosed;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Stops at the local deadline or when PDR requests termination.]

***********************************************************************/
static int Imc_PdrStop( void * pData )
{
    Imc_PdrItp_t * p = (Imc_PdrItp_t *)pData;
    return Abc_Clock() >= p->TimeStop || Pdr2_FrameIsStopped(p->pFrame);
}

/**Function*************************************************************

  Synopsis    [Allocates a positive SAT literal in a proof partition.]

***********************************************************************/
static int Imc_PdrNewVar( Imc_PdrItp_t * p, int iFrame )
{
    int Var = Vec_IntSize(p->vVarFrame);
    Vec_IntPush(p->vVarFrame, iFrame);
    return Abc_Var2Lit(Var, 0);
}

/**Function*************************************************************

  Synopsis    [Records an original proof clause and its owning frame.]

***********************************************************************/
static void Imc_PdrAddRoot( Imc_PdrItp_t * p, int iFrame, int * pLits, int nLits )
{
    Vec_Int_t * v = Vec_WecPushLevel(p->vClauses);
    int i;
    Vec_IntPush(p->vClauseFrame, iFrame);
    for ( i = 0; i < nLits; i++ )
        Vec_IntPush(v, pLits[i]);
}

/**Function*************************************************************

  Synopsis    [Splits a unit so it survives level-zero proof simplification.]

***********************************************************************/
static void Imc_PdrAddUnit( Imc_PdrItp_t * p, int iFrame, int Lit )
{
    int Lits[2];
    Lits[0] = Lit;
    Lits[1] = Imc_PdrNewVar(p, iFrame);
    Imc_PdrAddRoot(p, iFrame, Lits, 2);
    Lits[1] ^= 1;
    Imc_PdrAddRoot(p, iFrame, Lits, 2);
}

/**Function*************************************************************

  Synopsis    [Converts an ABC literal to a signed, one-based SAT literal.]

***********************************************************************/
static int Imc_PdrDimacs( int Lit )
{
    return (Abc_Lit2Var(Lit) + 1) * (Abc_LitIsCompl(Lit) ? -1 : 1);
}

/**Function*************************************************************

  Synopsis    [Finds the SAT variable for a register in an interpolant.]

***********************************************************************/
static int Imc_PdrStateVar( Gia_Man_t * pItp, int iReg )
{
    return Gia_ObjId(pItp, Gia_ManCi(pItp, iReg)) + 1;
}

/**Function*************************************************************

  Synopsis    [Translates a register cube literal into the interpolant SAT encoding.]

***********************************************************************/
static int Imc_PdrCubeLit( Gia_Man_t * pItp, int Lit )
{
    int Var = Imc_PdrStateVar(pItp, Abc_Lit2Var(Lit));
    return Abc_LitIsCompl(Lit) ? -Var : Var;
}

/**Function*************************************************************

  Synopsis    [Adds the three clauses defining a two-input AND.]

***********************************************************************/
static void Imc_PdrSatAnd( CCaDiCaL * pSat, int Out, int A, int B )
{
    ccadical_add(pSat, -Out); ccadical_add(pSat, A); ccadical_add(pSat, 0);
    ccadical_add(pSat, -Out); ccadical_add(pSat, B); ccadical_add(pSat, 0);
    ccadical_add(pSat, Out); ccadical_add(pSat, -A); ccadical_add(pSat, -B); ccadical_add(pSat, 0);
}

/**Function*************************************************************

  Synopsis    [Adds delta-frame clauses and frame-infinity clauses at one time.]

  Description [A clause stored at level k holds through level k. Omitting
  long clauses or reaching the cap only weakens this heuristic query.]

***********************************************************************/
static void Imc_PdrEncodeFrame( Imc_PdrItp_t * p, Vec_Int_t * vState, int iFrame )
{
    int Last = p->pFrame->iLevel + 1, k, i, j, Lit, nLits, Lits[64];
    const int * pLits;
    for ( k = Abc_MinInt(Last, Abc_MaxInt(1, iFrame)); k <= Last; k++ )
    {
        for ( i = 0; (nLits = Pdr2_FrameReadCube(p->pFrame, k, i, &pLits)) >= 0; i++ )
        {
            if ( p->nFrameClauses >= 20000 || ((i & 1023) == 0 && Imc_PdrStop(p)) )
                return;
            if ( !nLits || nLits > 64 ) continue;
            for ( j = 0; j < nLits; j++ )
            {
                Lit = pLits[j];
                Lits[j] = Vec_IntEntry(vState, Abc_Lit2Var(Lit)) ^ !Abc_LitIsCompl(Lit);
            }
            if ( j == 1 ) Imc_PdrAddUnit(p, iFrame, Lits[0]);
            else Imc_PdrAddRoot(p, iFrame, Lits, j);
            p->nFrameClauses++;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Builds a bounded, frame-strengthened transition query.]

  Description [Variables of the cut state are the only variables common
  to the left and right partitions. At time zero the registers are reset.
  An interior suffix starts from its PDR frame.]

***********************************************************************/
static void Imc_PdrEncodeSuffix( Imc_PdrItp_t * p, int First, int Last )
{
    Aig_Man_t * pAig = p->pFrame->pAig;
    int * pMap = ABC_ALLOC(int, Aig_ManObjNumMax(pAig));
    int i, t, Z, A, B, Lits[3];
    Vec_Int_t * v, * vNext;
    Aig_Obj_t * pObj;
    for ( t = First; t <= Last; t++ )
    {
        v = Vec_WecPushLevel(p->vStates);
        for ( i = 0; i < Aig_ManRegNum(pAig); i++ )
            Vec_IntPush(v, Imc_PdrNewVar(p, t));
    }
    for ( t = First; t <= Last && !Imc_PdrStop(p); t++ )
    {
        v = Vec_WecEntry(p->vStates, t - First);
        if ( t == 0 )
            for ( i = 0; i < Vec_IntSize(v); i++ )
                Imc_PdrAddUnit(p, t, Abc_LitNot(Vec_IntEntry(v, i)));
        Imc_PdrEncodeFrame(p, v, t);
        pMap[Aig_ObjId(Aig_ManConst1(pAig))] = Z = Imc_PdrNewVar(p, t);
        Imc_PdrAddUnit(p, t, Z);
        Saig_ManForEachPi( pAig, pObj, i )
            pMap[Aig_ObjId(pObj)] = Imc_PdrNewVar(p, t);
        Saig_ManForEachLo( pAig, pObj, i )
            pMap[Aig_ObjId(pObj)] = Vec_IntEntry(v, i);
        Aig_ManForEachNode( pAig, pObj, i )
        {
            A = pMap[Aig_ObjFaninId0(pObj)] ^ Aig_ObjFaninC0(pObj);
            B = pMap[Aig_ObjFaninId1(pObj)] ^ Aig_ObjFaninC1(pObj);
            pMap[i] = Z = Imc_PdrNewVar(p, t);
            Lits[0] = Abc_LitNot(Z); Lits[1] = A;
            Imc_PdrAddRoot(p, t, Lits, 2);
            Lits[1] = B;
            Imc_PdrAddRoot(p, t, Lits, 2);
            Lits[0] = Z; Lits[1] = Abc_LitNot(A); Lits[2] = Abc_LitNot(B);
            Imc_PdrAddRoot(p, t, Lits, 3);
        }
        if ( t == Last )
        {
            pObj = Aig_ManCo(pAig, 0);
            Imc_PdrAddUnit(p, t, pMap[Aig_ObjFaninId0(pObj)] ^ Aig_ObjFaninC0(pObj));
            break;
        }
        vNext = Vec_WecEntry(p->vStates, t + 1 - First);
        Saig_ManForEachLi( pAig, pObj, i )
        {
            A = pMap[Aig_ObjFaninId0(pObj)] ^ Aig_ObjFaninC0(pObj);
            Lits[0] = Abc_LitNot(A); Lits[1] = Vec_IntEntry(vNext, i);
            Imc_PdrAddRoot(p, t, Lits, 2);
            Lits[0] ^= 1; Lits[1] ^= 1;
            Imc_PdrAddRoot(p, t, Lits, 2);
        }
    }
    ABC_FREE(pMap);
}

/**Function*************************************************************

  Synopsis    [Checks one of the two Craig interpolant obligations.]

***********************************************************************/
static int Imc_PdrCheckCut( Imc_PdrItp_t * p, Gia_Man_t * pItp, Vec_Int_t * vGlobals, int Cut, int fLeft )
{
    CCaDiCaL * pSat = ccadical_init();
    int * pMap = ABC_ALLOC(int, Gia_ManObjNum(pItp));
    int MaxVar = Vec_IntSize(p->vVarFrame) + 1, i, k, Lit, A, B, Ret;
    Gia_Obj_t * pObj;
    Vec_Int_t * vClause;
    ccadical_set_terminate(pSat, p, Imc_PdrStop);
    Vec_WecForEachLevel( p->vClauses, vClause, i )
    {
        if ( (i & 1023) == 0 && Imc_PdrStop(p) ) { Ret = 0; goto cleanup; }
        if ( (Vec_IntEntry(p->vClauseFrame, i) < Cut) != fLeft ) continue;
        Vec_IntForEachEntry( vClause, Lit, k )
            ccadical_add(pSat, Imc_PdrDimacs(Lit));
        ccadical_add(pSat, 0);
    }
    pMap[0] = ++MaxVar;
    ccadical_add(pSat, -pMap[0]); ccadical_add(pSat, 0);
    Gia_ManForEachCi( pItp, pObj, i )
        pMap[Gia_ObjId(pItp, pObj)] = Vec_IntEntry(vGlobals, i) + 1;
    Gia_ManForEachAnd( pItp, pObj, i )
    {
        A = pMap[Gia_ObjFaninId0p(pItp, pObj)];
        B = pMap[Gia_ObjFaninId1p(pItp, pObj)];
        pMap[i] = ++MaxVar;
        Imc_PdrSatAnd(pSat, pMap[i], Gia_ObjFaninC0(pObj) ? -A : A, Gia_ObjFaninC1(pObj) ? -B : B);
    }
    pObj = Gia_ManCo(pItp, 0);
    A = pMap[Gia_ObjFaninId0p(pItp, pObj)];
    if ( Gia_ObjFaninC0(pObj) ) A = -A;
    ccadical_assume(pSat, fLeft ? -A : A);
    Ret = ccadical_solve(pSat);
cleanup:
    ccadical_release(pSat);
    ABC_FREE(pMap);
    return Ret == 20;
}

/**Function*************************************************************

  Synopsis    [Restricts a SAT model to states in F_i outside F_(i-1).]

  Description [Under F_i, violating F_(i-1) means violating at least one
  of the preceding delta clauses. At the first frame it means being
  different from the initial all-zero state.]

***********************************************************************/
static void Imc_PdrAddGap( Imc_PdrItp_t * p, CCaDiCaL * pSat, Gia_Man_t * pItp, int Cut )
{
    int Last = p->pFrame->iLevel + 1, MaxVar = Gia_ManObjNum(pItp) + 1;
    int i, j, k, Sel, nLits;
    Vec_Int_t * vSels;
    const int * pLits;
    for ( k = Cut; k <= Last; k++ )
    {
        for ( i = 0; (nLits = Pdr2_FrameReadCube(p->pFrame, k, i, &pLits)) >= 0; i++ )
        {
            if ( (i & 1023) == 0 && Imc_PdrStop(p) ) return;
            if ( !pLits ) continue;
            for ( j = 0; j < nLits; j++ )
                ccadical_add(pSat, -Imc_PdrCubeLit(pItp, pLits[j]));
            ccadical_add(pSat, 0);
        }
    }
    if ( Cut == 1 )
    {
        for ( i = 0; i < Aig_ManRegNum(p->pFrame->pAig); i++ )
            ccadical_add(pSat, Imc_PdrStateVar(pItp, i));
        ccadical_add(pSat, 0);
        return;
    }
    vSels = Vec_IntAlloc(32);
    for ( i = 0; (nLits = Pdr2_FrameReadCube(p->pFrame, Cut - 1, i, &pLits)) >= 0; i++ )
    {
        if ( (i & 1023) == 0 && Imc_PdrStop(p) ) break;
        if ( !pLits ) continue;
        Vec_IntPush(vSels, ++MaxVar);
        for ( j = 0; j < nLits; j++ )
        {
            ccadical_add(pSat, -MaxVar);
            ccadical_add(pSat, Imc_PdrCubeLit(pItp, pLits[j]));
            ccadical_add(pSat, 0);
        }
    }
    Vec_IntForEachEntry( vSels, Sel, i )
        ccadical_add(pSat, Sel);
    ccadical_add(pSat, 0);
    Vec_IntFree(vSels);
}

/**Function*************************************************************

  Synopsis    [Extracts a register cube sufficient to falsify the interpolant.]

  Description [For a false AND with two controlling inputs, select the
  input with the cheaper justification. A reverse sweep shares the
  justification of a gate reached by several paths.]

***********************************************************************/
static void Imc_PdrJustify( Gia_Man_t * pItp, CCaDiCaL * pSat, Vec_Int_t * vCube )
{
    int nObjs = Gia_ManObjNum(pItp);
    int Root = Gia_ObjFaninLit0p(pItp, Gia_ManCo(pItp, 0));
    int * pCost = ABC_CALLOC(int, nObjs);
    char * pUsed = ABC_CALLOC(char, nObjs), * pValue = ABC_CALLOC(char, nObjs);
    Gia_Obj_t * pObj;
    int i, Id, A, B, ValueA, ValueB;
    Vec_IntClear(vCube);
    Gia_ManForEachCi( pItp, pObj, i )
    {
        Id = Gia_ObjId(pItp, pObj);
        pValue[Id] = ccadical_val(pSat, Id + 1) > 0;
        pCost[Id] = 1;
    }
    Gia_ManForEachAnd( pItp, pObj, i )
    {
        A = Gia_ObjFaninId0p(pItp, pObj);
        B = Gia_ObjFaninId1p(pItp, pObj);
        ValueA = pValue[A] ^ Gia_ObjFaninC0(pObj);
        ValueB = pValue[B] ^ Gia_ObjFaninC1(pObj);
        pValue[i] = ValueA & ValueB;
        if ( ValueA && ValueB ) pCost[i] = Abc_MinInt(1024, pCost[A] + pCost[B]);
        else if ( ValueA )      pCost[i] = pCost[B];
        else if ( ValueB )      pCost[i] = pCost[A];
        else                    pCost[i] = Abc_MinInt(pCost[A], pCost[B]);
    }
    if ( (pValue[Abc_Lit2Var(Root)] ^ Abc_LitIsCompl(Root)) == 0 )
    {
        pUsed[Abc_Lit2Var(Root)] = 1;
        for ( i = nObjs - 1; i > 0; i-- )
        {
            pObj = Gia_ManObj(pItp, i);
            if ( !pUsed[i] || !Gia_ObjIsAnd(pObj) ) continue;
            A = Gia_ObjFaninId0p(pItp, pObj);
            B = Gia_ObjFaninId1p(pItp, pObj);
            ValueA = pValue[A] ^ Gia_ObjFaninC0(pObj);
            ValueB = pValue[B] ^ Gia_ObjFaninC1(pObj);
            if ( ValueA && ValueB ) pUsed[A] = pUsed[B] = 1;
            else if ( ValueA )      pUsed[B] = 1;
            else if ( ValueB )      pUsed[A] = 1;
            else                    pUsed[pCost[A] <= pCost[B] ? A : B] = 1;
        }
        Gia_ManForEachCi( pItp, pObj, i )
        {
            Id = Gia_ObjId(pItp, pObj);
            if ( pUsed[Id] ) Vec_IntPush(vCube, Abc_Var2Lit(i, !pValue[Id]));
        }
    }
    ABC_FREE(pCost);
    ABC_FREE(pUsed);
    ABC_FREE(pValue);
}

/**Function*************************************************************

  Synopsis    [Excludes the current register cube from subsequent gap queries.]

***********************************************************************/
static void Imc_PdrExcludeCube( CCaDiCaL * pSat, Gia_Man_t * pItp, Vec_Int_t * vCube )
{
    int i, Lit;
    Vec_IntForEachEntry( vCube, Lit, i )
        ccadical_add(pSat, -Imc_PdrCubeLit(pItp, Lit));
    ccadical_add(pSat, 0);
}

/**Function*************************************************************

  Synopsis    [Locally blocks states that violate both the interpolant and the preceding frame.]

  Description [Candidate enumeration is combinational. PDR checks each
  cube on the original transition relation before inserting it at Cut.]

***********************************************************************/
static void Imc_PdrStrengthen( Imc_PdrItp_t * p, Gia_Man_t * pItp, int Cut )
{
    int i, nTried = 0, nAdded = 0;
    CCaDiCaL * pSat;
    Vec_Int_t * vCube;
    Gia_Obj_t * pObj;
    if ( Cut < 1 || Cut > p->pFrame->iLevel || Imc_PdrStop(p) ||
         Gia_ManAndNum(pItp) > 30000 || Gia_ManCiNum(pItp) != Aig_ManRegNum(p->pFrame->pAig) )
        return;
    pSat = ccadical_init();
    ccadical_set_terminate(pSat, p, Imc_PdrStop);
    ccadical_add(pSat, -1); ccadical_add(pSat, 0);
    Gia_ManForEachAnd( pItp, pObj, i )
        Imc_PdrSatAnd(pSat, i + 1, Imc_PdrDimacs(Gia_ObjFaninLit0p(pItp, pObj)),
            Imc_PdrDimacs(Gia_ObjFaninLit1p(pItp, pObj)));
    ccadical_add(pSat, -Imc_PdrDimacs(Gia_ObjFaninLit0p(pItp, Gia_ManCo(pItp, 0))));
    ccadical_add(pSat, 0);
    Imc_PdrAddGap(p, pSat, pItp, Cut);
    vCube = Vec_IntAlloc(64);
    for ( i = 0; i < 12 && !p->fClosed && !Imc_PdrStop(p); i++ )
    {
        ccadical_limit(pSat, "conflicts", 300);
        if ( ccadical_solve(pSat) != 10 ) break;
        nTried++;
        Imc_PdrJustify(pItp, pSat, vCube);
        if ( !Vec_IntSize(vCube) ) break;
        Imc_PdrExcludeCube(pSat, pItp, vCube);
        if ( Vec_IntSize(vCube) > 48 || !Pdr2_FrameBlockCube(p->pFrame, Cut, vCube, 128, p->TimeStop, &p->fClosed) )
            continue;
        Imc_PdrExcludeCube(pSat, pItp, vCube);
        nAdded++;
    }
    if ( p->pPars->fVerbose )
        Abc_Print(1, "IMC: Local interpolation cut %d, %d gap states, %d relatively inductive cubes.\n", Cut, nTried, nAdded);
    Vec_IntFree(vCube);
    ccadical_release(pSat);
}

/**Function*************************************************************

  Synopsis    [Replays a single refutation across one register boundary.]

***********************************************************************/
static void Imc_PdrReadCut( Imc_PdrItp_t * p, FILE * pFile, Vec_Wec_t * vHints, int First, int Cut )
{
    int nVars = Vec_IntSize(p->vVarFrame), i, Lit, Frame;
    Vec_Int_t * vGlobals = Vec_IntDup(Vec_WecEntry(p->vStates, Cut - First)), * vClause;
    Imc_Prf_t * pProof;
    Gia_Man_t * pItp = NULL;
    Vec_IntForEachEntry( vGlobals, Lit, i )
        Vec_IntWriteEntry(vGlobals, i, Abc_Lit2Var(Lit));
    pProof = Imc_PrfStart(vGlobals, 0, nVars, 0, 0, 0);
    Vec_IntForEachEntry( p->vVarFrame, Frame, i )
        Imc_PrfSetVar(pProof, i, Frame < Cut);
    Vec_WecForEachLevel( p->vClauses, vClause, i )
    {
        if ( (i & 1023) == 0 && Imc_PdrStop(p) ) goto cleanup;
        Imc_PrfAddRoot(pProof, Vec_IntArray(vClause), Vec_IntSize(vClause), Vec_IntEntry(p->vClauseFrame, i) < Cut);
    }
    pItp = Imc_PrfRead(pProof, pFile, nVars, 0, 0, p->TimeStop);
    if ( pItp )
    {
        if ( p->pPars->fCheck && (!Imc_PdrCheckCut(p, pItp, vGlobals, Cut, 1) ||
                                  !Imc_PdrCheckCut(p, pItp, vGlobals, Cut, 0)) )
        {
            if ( !Imc_PdrStop(p) ) Abc_Print(-1, "IMC: Interpolant verification failed at PDR frame %d.\n", Cut);
            goto cleanup;
        }
        p->nCuts++;
        Imc_ManCollectHintCubes(pItp, vHints);
        Imc_PdrStrengthen(p, pItp, Cut);
    }
cleanup:
    Gia_ManStopP(&pItp);
    Imc_PrfStop(pProof);
    Vec_IntFree(vGlobals);
}

/**Function*************************************************************

  Synopsis    [Interpolates a bounded suffix of the current clausal trace.]

  Description [SAT and UNKNOWN only influence the next heuristic query.
  UNSAT supplies a proof for the shared-register cuts. Only PDR can
  report completion of the property.]

***********************************************************************/
static int Imc_PdrSolveSuffix( Imc_PdrItp_t * p, Vec_Wec_t * vHints, int First, int Last )
{
    CCaDiCaL * pSat = NULL;
    FILE * pFile = NULL;
    Vec_Int_t * vClause;
    int i, j, Lit, Cut, Result = 0, fTracing = 0;
    p->vClauses = Vec_WecAlloc(1024);
    p->vClauseFrame = Vec_IntAlloc(1024);
    p->vStates = Vec_WecAlloc(16);
    p->vVarFrame = Vec_IntStart(1);
    p->nFrameClauses = 0;
    Imc_PdrEncodeSuffix(p, First, Last);
    if ( Imc_PdrStop(p) || !(pFile = Imc_ProofFile()) ) goto cleanup;
    pSat = ccadical_init();
    ccadical_set_option(pSat, "lrat", 1);
    ccadical_set_option(pSat, "binary", 1);
    if ( !(fTracing = ccadical_trace_proof(pSat, pFile, "imc-frame-lrat")) ) goto cleanup;
    ccadical_set_terminate(pSat, p, Imc_PdrStop);
    ccadical_limit(pSat, "conflicts", 3500);
    Vec_WecForEachLevel( p->vClauses, vClause, i )
    {
        Vec_IntForEachEntry( vClause, Lit, j )
            ccadical_add(pSat, Imc_PdrDimacs(Lit));
        ccadical_add(pSat, 0);
        if ( (i & 1023) == 0 && Imc_PdrStop(p) ) goto cleanup;
    }
    Result = ccadical_solve(pSat);
    ccadical_close_proof(pSat);
    fTracing = 0;
    if ( Result == 20 )
        for ( Cut = First + 1; Cut <= Last && !p->fClosed && !Imc_PdrStop(p); Cut++ )
        {
            if ( Last - First > 4 && Cut != First + 1 && Cut != Last && Cut != (First + Last) / 2 )
                continue;
            Imc_PdrReadCut(p, pFile, vHints, First, Cut);
        }
cleanup:
    if ( fTracing ) ccadical_close_proof(pSat);
    if ( pSat ) ccadical_release(pSat);
    if ( pFile ) fclose(pFile);
    Vec_WecFree(p->vClauses);
    Vec_IntFree(p->vClauseFrame);
    Vec_WecFree(p->vStates);
    Vec_IntFree(p->vVarFrame);
    return Result;
}

/**Function*************************************************************

  Synopsis    [Tries short suffixes when PDR opens selected levels.]

***********************************************************************/
static int Imc_PdrFrame( const Pdr2_Frame_t * pFrame, Vec_Wec_t * vHints, void * pData )
{
    int Level = pFrame->iLevel, Len, Result = 0, nTries = 0;
    int nBefore = Vec_WecSize(vHints);
    abctime Start;
    Imc_PdrItp_t Itp;
    if ( (Level != 4 && Level != 12 && Level != 32 && Level != 64) ||
          Aig_ManRegNum(pFrame->pAig) > 256 || Aig_ManNodeNum(pFrame->pAig) > 10000 )
        return 0;
    memset(&Itp, 0, sizeof(Itp));
    Itp.pFrame = pFrame;
    Itp.pPars = (Imc_Par_t *)pData;
    Start = Abc_Clock();
    Itp.TimeStop = Start + 4 * (abctime)CLOCKS_PER_SEC;
    if ( pFrame->TimeStop && pFrame->TimeStop < Itp.TimeStop ) Itp.TimeStop = pFrame->TimeStop;
    for ( Len = 2; Len <= Abc_MinInt(Level, 8) && !Imc_PdrStop(&Itp); Len *= 2 )
    {
        nTries++;
        Result = Imc_PdrSolveSuffix(&Itp, vHints, Level - Len, Level);
        if ( Result != 10 ) break;
    }
    if ( Itp.pPars->fVerbose )
        Abc_Print(1, "IMC: Frame feedback level %d, suffix searches %d, last result %d, proof cuts %d, new cubes %d, %.3f s.\n",
            Level, nTries, Result, Itp.nCuts, Vec_WecSize(vHints) - nBefore, (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC);
    return Itp.fClosed;
}

/**Function*************************************************************

  Synopsis    [Runs concrete PDR with interpolation at selected frames.]

***********************************************************************/
int Imc_ManSolvePdrFrames( Aig_Man_t * pAig, Vec_Wec_t * vCubes, abctime TimeStop, int * piFrame, Imc_Par_t * pPars )
{
    return Pdr2_ManSolveFrameHints(pAig, vCubes, TimeStop, Imc_ManStopId, piFrame,
        pPars->fVerbose, Imc_PdrFrame, pPars);
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
