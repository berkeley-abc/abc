/**CFile****************************************************************

  FileName    [imcSat.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Interpolation-based model checking.]

  Synopsis    [SAT encoding, image computation, and induction.]

  Author      [ABC contributors]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 23, 2026.]

  Revision    [$Id: imcSat.c,v 1.00 2026/10/23 00:00:00 alanmi Exp $]

***********************************************************************/

#include "imcInt.h"
#include "opt/dar/dar.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates a SAT variable and records its interpolation partition.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Imc_SatNewVar( Imc_Sat_t * p, int fPartA )
{
    int Var = p->nVars++;
    if ( p->pCad )
        Imc_PrfSetVar( p->pPrf, Var, fPartA );
    else if ( p->pSat2 )
    {
        sat_solver2_setnvars( p->pSat2, p->nVars );
        var_set_partA( p->pSat2, Var, fPartA ^ p->fDual );
    }
    else
        sat_solver_setnvars( p->pSat, p->nVars );
    return Var;
}

/**Function*************************************************************

  Synopsis    [Maps a template key to a lazily allocated SAT variable.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_SatVar( Imc_Sat_t * p, int Key, int fPartA )
{
    int Var;
    if ( p->vMap == NULL )
        return Key;
    Var = Vec_IntEntry( p->vMap, Key );
    if ( Var < 0 )
    {
        Var = Imc_SatNewVar( p, fPartA );
        Vec_IntWriteEntry( p->vMap, Key, Var );
    }
    return Var;
}

/**Function*************************************************************

  Synopsis    [Normalizes and adds a clause while preserving proof-root labels.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Imc_SatAddClause( Imc_Sat_t * p, int * pLits, int nLits, int fPartA )
{
    if ( p->pSat2 || p->pCad )
    {
        int Cid, i, k;
        // CaDiCaL emits a replacement ID when it simplifies duplicate
        // literals. Normalize before registering either solver's roots.
        for ( i = 1; i < nLits; i++ )
            for ( k = 0; k < i; k++ )
            {
                if ( pLits[i] == (pLits[k] ^ 1) )
                    return;
                if ( pLits[i] == pLits[k] )
                {
                    Vec_Int_t * vClean = Vec_IntAlloc( nLits );
                    for ( k = 0; k < nLits; k++ )
                        Vec_IntPushUnique( vClean, pLits[k] );
                    Imc_SatAddClause( p, Vec_IntArray(vClean), Vec_IntSize(vClean), fPartA );
                    Vec_IntFree( vClean );
                    return;
                }
            }
        assert( nLits > 0 );
        // Delay propagation until all roots have their partition labels.
        // The proof solver labels clauses after insertion; a unit inserted
        // earlier could otherwise simplify a later, still unlabelled root.
        // LRAT also needs all original IDs allocated before propagation
        // derives new clauses. LIDRUP can represent interleaved IDs.
        if ( nLits == 1 && (p->pSat2 || p->pProof == NULL) )
        {
            int Lits[2] = { pLits[0], Abc_Var2Lit(Imc_SatNewVar(p, fPartA), 0) };
            Imc_SatAddClause( p, Lits, 2, fPartA );
            Lits[1] = Abc_LitNot(Lits[1]);
            Imc_SatAddClause( p, Lits, 2, fPartA );
            return;
        }
        if ( p->vCapture )
        {
            Vec_IntPush( p->vCapture, nLits );
            for ( i = 0; i < nLits; i++ )
                Vec_IntPush( p->vCapture, pLits[i] );
        }
        if ( p->pCad )
        {
            Imc_PrfAddRoot( p->pPrf, pLits, nLits, fPartA );
            for ( i = 0; i < nLits; i++ )
                ccadical_add( p->pCad, (Abc_Lit2Var(pLits[i])+1) * (Abc_LitIsCompl(pLits[i]) ? -1 : 1) );
            ccadical_add( p->pCad, 0 );
        }
        else
        {
            int Id = Imc_PrfAddRoot( p->pPrf, pLits, nLits, fPartA );
            Cid = sat_solver2_addclause( p->pSat2, pLits, pLits + nLits, Id );
            clause2_set_id( p->pSat2, Cid, Id );
            clause2_set_partA( p->pSat2, Cid, fPartA );
        }
    }
    else if ( !p->fUnsat && !sat_solver_addclause(p->pSat, pLits, pLits + nLits) )
        p->fUnsat = 1;
}

/**Function*************************************************************

  Synopsis    [Adds a CNF with a variable offset and partition label.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Imc_SatAddCnf( Imc_Sat_t * p, Cnf_Dat_t * pCnf, int Offset, int fPartA )
{
    Vec_Int_t * vLits = Vec_IntAlloc( 32 );
    int i, * pLit;
    for ( i = 0; i < pCnf->nClauses; i++ )
    {
        Vec_IntClear( vLits );
        for ( pLit = pCnf->pClauses[i]; pLit < pCnf->pClauses[i+1]; pLit++ )
            Vec_IntPush( vLits, *pLit + 2 * Offset );
        Imc_SatAddClause( p, Vec_IntArray(vLits), Vec_IntSize(vLits), fPartA );
    }
    Vec_IntFree( vLits );
}

/**Function*************************************************************

  Synopsis    [Indexes the consecutive defining clauses of each mapped CNF variable.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Imc_CnfMap( Cnf_Dat_t * pCnf, Vec_Int_t ** pvStart, Vec_Int_t ** pvCount )
{
    int i, Var;
    Vec_IntFreeP( pvStart );
    Vec_IntFreeP( pvCount );
    *pvStart = Vec_IntStartFull( pCnf->nVars );
    *pvCount = Vec_IntStart( pCnf->nVars );
    // Cnf_Derive places the defined variable first in each clause and
    // writes the clauses of each definition consecutively.
    for ( i = 0; i < pCnf->nClauses; i++ )
    {
        Var = Abc_Lit2Var( pCnf->pClauses[i][0] );
        if ( Vec_IntEntry(*pvStart, Var) == -1 )
            Vec_IntWriteEntry( *pvStart, Var, i );
        assert( Vec_IntEntry(*pvStart, Var) + Vec_IntEntry(*pvCount, Var) == i );
        Vec_IntAddToEntry( *pvCount, Var, 1 );
    }
}

/**Function*************************************************************

  Synopsis    [Loads only the mapped transition cone needed by an output.]

  Description [Unused transition outputs impose no restriction on the
  current state. Omitting their definitions preserves the image query
  and avoids irrelevant decisions and proof clauses.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_SatLoadCnfCone( Imc_Sat_t * pSat, Cnf_Dat_t * pCnf, Vec_Int_t * vStart, Vec_Int_t * vCount, Vec_Str_t ** pvLoaded, int Var, int Offset, int fPartA )
{
    Vec_Int_t * vStack = Vec_IntAlloc( 32 );
    Vec_Int_t * vLits = Vec_IntAlloc( 16 );
    int i, Start, Count, * pLit;
    if ( *pvLoaded == NULL )
        *pvLoaded = Vec_StrStart( pCnf->nVars );
    Vec_IntPush( vStack, Var );
    while ( Vec_IntSize(vStack) )
    {
        Var = Vec_IntPop( vStack );
        if ( Vec_StrEntry(*pvLoaded, Var) )
            continue;
        Vec_StrWriteEntry( *pvLoaded, Var, 1 );
        Start = Vec_IntEntry( vStart, Var );
        Count = Vec_IntEntry( vCount, Var );
        for ( i = Start; i < Start + Count; i++ )
        {
            Vec_IntClear( vLits );
            for ( pLit = pCnf->pClauses[i]; pLit < pCnf->pClauses[i+1]; pLit++ )
            {
                Vec_IntPush( vLits, Abc_Var2Lit(Imc_SatVar(pSat, Abc_Lit2Var(*pLit) + Offset, fPartA), Abc_LitIsCompl(*pLit)) );
                if ( pLit != pCnf->pClauses[i] )
                    Vec_IntPush( vStack, Abc_Lit2Var(*pLit) );
            }
            Imc_SatAddClause( pSat, Vec_IntArray(vLits), Vec_IntSize(vLits), fPartA );
        }
    }
    Vec_IntFree( vStack );
    Vec_IntFree( vLits );
}

/**Function*************************************************************

  Synopsis    [Loads the transition definitions needed by one SAT variable.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_SatLoadCone( Imc_Sat_t * pSat, Imc_Man_t * p, int Var, int fPartA )
{
    Imc_SatLoadCnfCone( pSat, p->pCnf, p->vCnfStart, p->vCnfCount, &pSat->vLoaded, Var, 0, fPartA );
}

/**Function*************************************************************

  Synopsis    [Encodes an AND relation in the selected SAT partition.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_SatAddAnd( Imc_Sat_t * p, int Lit, int Lit0, int Lit1, int fPartA )
{
    int Lits[3];
    Lits[0] = Abc_LitNot(Lit); Lits[1] = Lit0;
    Imc_SatAddClause( p, Lits, 2, fPartA );
    Lits[1] = Lit1;
    Imc_SatAddClause( p, Lits, 2, fPartA );
    Lits[0] = Lit; Lits[1] = Abc_LitNot(Lit0); Lits[2] = Abc_LitNot(Lit1);
    Imc_SatAddClause( p, Lits, 3, fPartA );
}

/**Function*************************************************************

  Synopsis    [Encodes a combinational GIA over the supplied SAT variables.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Imc_SatAddGia( Imc_Sat_t * p, Gia_Man_t * pGia, Vec_Int_t * vVars, int fPartA )
{
    Gia_Obj_t * pObj;
    int i, Lit;
    assert( Gia_ManCiNum(pGia) == Vec_IntSize(vVars) );
    Lit = Abc_Var2Lit( Imc_SatNewVar(p, fPartA), 1 );
    Imc_SatAddClause( p, &Lit, 1, fPartA );
    Gia_ManConst0(pGia)->Value = Abc_LitNot(Lit);
    Gia_ManForEachCi( pGia, pObj, i )
        pObj->Value = Abc_Var2Lit( Vec_IntEntry(vVars, i), 0 );
    Gia_ManForEachAnd( pGia, pObj, i )
    {
        pObj->Value = Abc_Var2Lit( Imc_SatNewVar(p, fPartA), 0 );
        Imc_SatAddAnd( p, pObj->Value, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj), fPartA );
    }
    return Gia_ObjFanin0Copy( Gia_ManPo(pGia, 0) );
}

/**Function*************************************************************

  Synopsis    [Replaces the cached frontier CNF and its used-input maps.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Imc_ManSetFront( Imc_Man_t * p, Gia_Man_t * pFront )
{
    Aig_Man_t * pAig = Gia_ManToAigSimple( pFront );
    Vec_Str_t * vUsed;
    int i, * pLit;
    if ( p->pCnfF )
        Cnf_DataFree( p->pCnfF );
    Vec_IntFreeP( &p->vFrontVars );
    Vec_IntFreeP( &p->vFrontUsed );
    p->pCnfF = Cnf_Derive( pAig, 1 );
    p->vFrontVars = Vec_IntAlloc( Aig_ManCiNum(pAig) );
    for ( i = 0; i < Aig_ManCiNum(pAig); i++ )
        Vec_IntPush( p->vFrontVars, p->pCnfF->pVarNums[Aig_ManCi(pAig, i)->Id] );
    vUsed = Vec_StrStart( p->pCnfF->nVars );
    for ( pLit = p->pCnfF->pClauses[0]; pLit < p->pCnfF->pClauses[p->pCnfF->nClauses]; pLit++ )
        Vec_StrWriteEntry( vUsed, Abc_Lit2Var(*pLit), 1 );
    p->vFrontUsed = Vec_IntAlloc( Aig_ManCiNum(pAig) );
    for ( i = 0; i < Aig_ManCiNum(pAig); i++ )
        if ( Vec_StrEntry(vUsed, Vec_IntEntry(p->vFrontVars, i)) )
            Vec_IntPush( p->vFrontUsed, i );
    Vec_StrFree( vUsed );
    p->iFront = p->pCnfF->pVarNums[Aig_ManCo(pAig, 0)->Id];
    Aig_ManStop( pAig );
}

/**Function*************************************************************

  Synopsis    [Adds the current frontier over the supplied state variables.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_SatAddFront( Imc_Sat_t * pSat, Imc_Man_t * p, Vec_Int_t * vVars, int fPartA )
{
    Vec_Int_t * vMap = Vec_IntStartFull( p->pCnfF->nVars );
    Vec_Int_t * vLits = Vec_IntAlloc( 16 );
    int i, Reg, Var, Lit, * pLit;
    Vec_IntForEachEntry( p->vFrontUsed, Reg, i )
    {
        Var = Vec_IntEntry( p->vFrontVars, Reg );
        Vec_IntWriteEntry( vMap, Var, Imc_SatVar(pSat, Vec_IntEntry(vVars, Reg), fPartA) );
    }
    for ( i = 0; i < p->pCnfF->nClauses; i++ )
    {
        Vec_IntClear( vLits );
        for ( pLit = p->pCnfF->pClauses[i]; pLit < p->pCnfF->pClauses[i+1]; pLit++ )
        {
            Var = Abc_Lit2Var( *pLit );
            if ( Vec_IntEntry(vMap, Var) == -1 )
                Vec_IntWriteEntry( vMap, Var, Imc_SatNewVar(pSat, fPartA) );
            Vec_IntPush( vLits, Abc_Var2Lit(Vec_IntEntry(vMap, Var), Abc_LitIsCompl(*pLit)) );
        }
        if ( pSat->iGuard )
            Vec_IntPush( vLits, Abc_Var2Lit(pSat->iGuard, 1) );
        Imc_SatAddClause( pSat, Vec_IntArray(vLits), Vec_IntSize(vLits), fPartA );
    }
    Lit = Abc_Var2Lit( Vec_IntEntry(vMap, p->iFront), 0 );
    if ( pSat->iGuard )
    {
        int Pair[2] = { Abc_Var2Lit(pSat->iGuard, 1), Lit };
        Imc_SatAddClause( pSat, Pair, 2, fPartA );
        Lit = Abc_Var2Lit( pSat->iGuard, 0 );
    }
    Vec_IntFree( vMap );
    Vec_IntFree( vLits );
    return Lit;
}

/**Function*************************************************************

  Synopsis    [Extracts a trace from a SAT model and optionally verifies it.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Abc_Cex_t * Imc_ManReadCex( Imc_Man_t * p, sat_solver * pSat, sat_solver2 * pSat2, CCaDiCaL * pCad, Vec_Int_t * vMap, int iFrame, int iStart, int fQuiet, int fVerify )
{
    Abc_Cex_t * pCex = Abc_CexAlloc( Gia_ManRegNum(p->pGia), Gia_ManPiNum(p->pGia), iFrame - iStart + 1 );
    int i, f, Var, Value;
    pCex->iPo = 0;
    pCex->iFrame = iFrame - iStart;
    for ( f = iStart; f <= iFrame; f++ )
        Vec_IntForEachEntry( p->vPis, Var, i )
        {
            if ( p->pPars->fBackward && pSat == NULL )
            {
                if ( f == iFrame )
                    continue;
                if ( f < iFrame - 1 )
                    Var = Vec_IntEntry( p->vImagePis, f * Gia_ManPiNum(p->pGia) + i );
            }
            else if ( f )
                Var = Vec_IntEntry( p->vImagePis, f * Gia_ManPiNum(p->pGia) + i );
            if ( vMap )
                Var = Vec_IntEntry( vMap, Var );
            Value = Var < 0 ? 0 : pCad ? ccadical_val(pCad, Var+1) > 0 : pSat2 ? sat_solver2_var_value(pSat2, Var) : sat_solver_var_value(pSat, Var);
            if ( Value )
                Imc_CexSetBit( pCex->pData, pCex->nRegs + (f - iStart) * pCex->nPis + i );
        }
    if ( fVerify && !Gia_ManVerifyCex(p->pGia, pCex, 0) )
    {
        if ( !fQuiet )
            Abc_Print( -1, "IMC: Counterexample verification failed.\n" );
        Abc_CexFree( pCex );
        return NULL;
    }
    return pCex;
}

/**Function*************************************************************

  Synopsis    [Checks initiation, consecution, and safety independently.]

  Description [For backward reachability, the invariant is the complement
  of the union of frontiers. This check uses a fresh SAT solver and the
  full transition relation, independently of the lazy image encoding.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_ManCheckInvariantInt( Imc_Man_t * p, Gia_Man_t * pReached, int fSafety )
{
    Imc_Sat_t Sat;
    Gia_Obj_t * pObj;
    int i, LitOld, LitNew, Lits[2], Status, Result = 0;
    memset(&Sat, 0, sizeof(Sat));
    // All original registers start at zero.
    Gia_ManConst0(pReached)->Value = 0;
    Gia_ManForEachCi( pReached, pObj, i )
        pObj->Value = 0;
    Gia_ManForEachAnd( pReached, pObj, i )
        pObj->Value = (Gia_ObjFanin0(pObj)->Value ^ Gia_ObjFaninC0(pObj)) & (Gia_ObjFanin1(pObj)->Value ^ Gia_ObjFaninC1(pObj));
    pObj = Gia_ManCo( pReached, 0 );
    if ( !(Gia_ObjFanin0(pObj)->Value ^ Gia_ObjFaninC0(pObj) ^ p->pPars->fBackward) )
    {
        Abc_Print( -1, "IMC: Invariant excludes the initial state.\n" );
        return 0;
    }
    Sat.pSat = sat_solver_new();
    Sat.nVars = p->pCnf->nVars;
    sat_solver_setnvars( Sat.pSat, Sat.nVars );
    sat_solver_set_runtime_limit( Sat.pSat, p->TimeStop );
    Imc_SatAddCnf( &Sat, p->pCnf, 0, 0 );
    LitOld = Imc_SatAddGia( &Sat, pReached, p->vRos, 0 ) ^ p->pPars->fBackward;
    LitNew = Imc_SatAddGia( &Sat, pReached, p->vRis, 0 ) ^ p->pPars->fBackward;
    Lits[0] = LitOld;
    Lits[1] = Abc_Var2Lit( p->iBad, 0 );
    Status = !fSafety || Sat.fUnsat ? l_False : sat_solver_solve( Sat.pSat, Lits, Lits + 2, p->pPars->nConfLimit, 0, 0, 0 );
    if ( fSafety && Status != l_False )
    {
        Abc_Print( -1, "IMC: Invariant safety check %s.\n", Status == l_True ? "failed" : "timed out" );
        goto finish;
    }
    Lits[1] = Abc_LitNot( LitNew );
    Status = Sat.fUnsat ? l_False : sat_solver_solve( Sat.pSat, Lits, Lits + 2, p->pPars->nConfLimit, 0, 0, 0 );
    if ( Status != l_False )
    {
        Abc_Print( -1, "IMC: Invariant induction check %s.\n", Status == l_True ? "failed" : "timed out" );
        goto finish;
    }
    Result = 1;
finish:
    sat_solver_delete( Sat.pSat );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Independently checks invariant initiation, induction, and safety.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Imc_ManCheckInvariant( Imc_Man_t * p, Gia_Man_t * pReached )
{
    return Imc_ManCheckInvariantInt( p, pReached, 1 );
}

/**Function*************************************************************

  Synopsis    [Independently checks initiation and induction of a state restriction.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Imc_ManCheckInductive( Imc_Man_t * p, Gia_Man_t * pInvariant )
{
    return Imc_ManCheckInvariantInt( p, pInvariant, 0 );
}

/**Function*************************************************************

  Synopsis    [Builds and simplifies the shared suffix once per BMC depth.]

  Description [Structural hashing across frames propagates constants and
  removes unused next-state cones. The initial state inputs are mapped
  directly onto the shared variables of the image transition.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_ManBuildSuffixFwd( Imc_Man_t * p, int nFrames )
{
    Gia_Man_t * pNew = Gia_ManStart( Gia_ManObjNum(p->pGia) );
    Gia_Man_t * pTemp;
    Gia_Obj_t * pObj;
    Aig_Man_t * pAig;
    Vec_Int_t * vState = Vec_IntAlloc( Gia_ManRegNum(p->pGia) );
    Vec_Int_t * vBad = Vec_IntAlloc( nFrames );
    int i, f, Lit, Var, iFail = 0, nRegs = Gia_ManRegNum(p->pGia);
    Imc_ManImageStop( p );
    p->nImageCalls = 0;
    if ( p->pCnfB )
        Cnf_DataFree( p->pCnfB );
    p->pCnfB = NULL;
    Vec_IntFreeP( &p->vMapB );
    Vec_IntFreeP( &p->vImagePis );
    Vec_IntFreeP( &p->vImageBad );
    Vec_IntFreeP( &p->vSharedUsed );
    Vec_IntFreeP( &p->vPrefix );
    pNew->fAddStrash = 1;
    Gia_ManHashStart( pNew );
    for ( i = 0; i < nRegs; i++ )
    {
        Lit = Gia_ManAppendCi( pNew );
        Vec_IntPush( vState, Lit );
    }
    for ( f = 0; f < nFrames; f++ )
    {
        if ( p->TimeStop && Abc_Clock() >= p->TimeStop )
            goto finish;
        Gia_ManConst0(p->pGia)->Value = 0;
        Gia_ManForEachPi( p->pGia, pObj, i )
            pObj->Value = Gia_ManAppendCi( pNew );
        Gia_ManForEachRo( p->pGia, pObj, i )
            pObj->Value = Vec_IntEntry( vState, i );
        Gia_ManForEachAnd( p->pGia, pObj, i )
            pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        Lit = Gia_ObjFanin0Copy( Gia_ManPo(p->pGia, 0) );
        Vec_IntPush( vBad, Lit );
        iFail = Gia_ManHashOr( pNew, iFail, Lit );
        Gia_ManForEachRi( p->pGia, pObj, i )
            Vec_IntWriteEntry( vState, i, Gia_ObjFanin0Copy(pObj) );
    }
    Gia_ManAppendCo( pNew, iFail );
    Vec_IntForEachEntry( vBad, Lit, i )
        Gia_ManAppendCo( pNew, Lit );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    pAig = Gia_ManToAigSimple( pNew );
    p->pCnfB = Cnf_Derive( pAig, Aig_ManCoNum(pAig) );
    if ( p->pPars->fVerbose )
        Abc_Print( 1, "IMC: Suffix depth = %d  variables = %d  clauses = %d.\n", nFrames, p->pCnfB->nVars, p->pCnfB->nClauses );
    p->vMapB = Vec_IntAlloc( p->pCnfB->nVars );
    for ( i = 0; i < p->pCnfB->nVars; i++ )
        Vec_IntPush( p->vMapB, p->pCnf->nVars + i );
    p->vPrefix = Vec_IntAlloc( nRegs );
    for ( i = 0; i < nRegs; i++ )
    {
        Var = p->pCnfB->pVarNums[Aig_ManCi(pAig, i)->Id];
        Vec_IntPush( p->vPrefix, Var );
        if ( !p->pPars->fAbstract || p->pPred == NULL )
            Vec_IntWriteEntry( p->vMapB, Var, Vec_IntEntry(p->vRis, i) );
    }
    {
        Vec_Str_t * vUsed = Vec_StrStart( p->pCnfB->nVars );
        int * pLit;
        for ( pLit = p->pCnfB->pClauses[0]; pLit < p->pCnfB->pClauses[p->pCnfB->nClauses]; pLit++ )
            Vec_StrWriteEntry( vUsed, Abc_Lit2Var(*pLit), 1 );
        p->vSharedUsed = Vec_IntAlloc( nRegs );
        for ( i = 0; i < nRegs; i++ )
            if ( Vec_StrEntry(vUsed, p->pCnfB->pVarNums[Aig_ManCi(pAig, i)->Id]) )
                Vec_IntPush( p->vSharedUsed, i );
        Vec_StrFree( vUsed );
    }
    p->vImagePis = Vec_IntAlloc( Vec_IntSize(p->vPis) + Aig_ManCiNum(pAig) );
    Vec_IntForEachEntry( p->vPis, Var, i )
        Vec_IntPush( p->vImagePis, Var );
    for ( i = nRegs; i < Aig_ManCiNum(pAig); i++ )
    {
        Var = p->pCnfB->pVarNums[Aig_ManCi(pAig, i)->Id];
        Vec_IntPush( p->vImagePis, Vec_IntEntry(p->vMapB, Var) );
    }
    p->vImageBad = Vec_IntAlloc( nFrames + 1 );
    for ( i = 0; i < Aig_ManCoNum(pAig); i++ )
    {
        Var = p->pCnfB->pVarNums[Aig_ManCo(pAig, i)->Id];
        Vec_IntPush( p->vImageBad, Vec_IntEntry(p->vMapB, Var) );
    }
    Aig_ManStop( pAig );
finish:
    Gia_ManStop( pNew );
    Vec_IntFree( vState );
    Vec_IntFree( vBad );
    return p->pCnfB != NULL;
}

/**Function*************************************************************

  Synopsis    [Builds the backward reachable-prefix encoding.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_ManBuildPrefix( Imc_Man_t * p, int nFrames )
{
    // With optional resets, the final state is reachable at any depth
    // below nFrames. Truncating a satisfying trace after its last reset
    // recovers a trace of the original system. This retains all shorter
    // depths without a separate boundary selector for each frame.
    Gia_Man_t * pNew = Gia_ManStart( Gia_ManObjNum(p->pGia) ), * pTemp;
    Gia_Obj_t * pObj;
    Aig_Man_t * pAig;
    Vec_Int_t * vState = Vec_IntStart( Gia_ManRegNum(p->pGia) );
    Vec_Int_t * vOutputs = Vec_IntAlloc( nFrames * Gia_ManRegNum(p->pGia) );
    Vec_Int_t * vPis = Vec_IntAlloc( 100 );
    Vec_Int_t * vResets = Vec_IntAlloc( nFrames );
    int i, f, Lit, Var, Reset;
    Imc_ManImageStop( p );
    p->nImageCalls = 0;
    if ( p->pCnfB )
        Cnf_DataFree( p->pCnfB );
    p->pCnfB = NULL;
    Vec_IntFreeP( &p->vImagePis );
    Vec_IntFreeP( &p->vImageBad );
    Vec_IntFreeP( &p->vPrefix );
    Vec_IntFreeP( &p->vResets );
    Gia_ManHashStart( pNew );
    pNew->fAddStrash = 1;
    for ( f = 0; f < nFrames; f++ )
    {
        if ( p->TimeStop && Abc_Clock() >= p->TimeStop )
            goto finish;
        if ( !p->pPars->fResetPrefix || f == nFrames - 1 )
            Vec_IntForEachEntry( vState, Lit, i )
                Vec_IntPush( vOutputs, Lit );
        if ( f == nFrames - 1 )
            break;
        Gia_ManConst0(p->pGia)->Value = 0;
        Gia_ManForEachPi( p->pGia, pObj, i )
        {
            Vec_IntPush( vPis, Gia_ManCiNum(pNew) );
            pObj->Value = Gia_ManAppendCi( pNew );
        }
        Reset = 0;
        if ( p->pPars->fResetPrefix )
        {
            Vec_IntPush( vResets, Gia_ManCiNum(pNew) );
            Reset = Gia_ManAppendCi( pNew );
        }
        Gia_ManForEachRo( p->pGia, pObj, i )
            pObj->Value = Vec_IntEntry( vState, i );
        Gia_ManForEachAnd( p->pGia, pObj, i )
            pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        Gia_ManForEachRi( p->pGia, pObj, i )
            Vec_IntWriteEntry( vState, i, Gia_ManHashAnd(pNew, Gia_ObjFanin0Copy(pObj), Abc_LitNot(Reset)) );
    }
    Vec_IntForEachEntry( vOutputs, Lit, i )
        Gia_ManAppendCo( pNew, Lit );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    pAig = Gia_ManToAigSimple( pNew );
    p->pCnfB = Cnf_Derive( pAig, Aig_ManCoNum(pAig) );
    Imc_CnfMap( p->pCnfB, &p->vCnfStartB, &p->vCnfCountB );
    p->vImagePis = Vec_IntAlloc( Aig_ManCiNum(pAig) );
    Vec_IntForEachEntry( vPis, Lit, i )
    {
        Var = p->pCnfB->pVarNums[Aig_ManCi(pAig, Lit)->Id];
        Vec_IntPush( p->vImagePis, p->pCnf->nVars + Var );
    }
    p->vResets = Vec_IntAlloc( Vec_IntSize(vResets) );
    Vec_IntForEachEntry( vResets, Lit, i )
    {
        Var = p->pCnfB->pVarNums[Aig_ManCi(pAig, Lit)->Id];
        Vec_IntPush( p->vResets, p->pCnf->nVars + Var );
    }
    p->vPrefix = Vec_IntAlloc( Aig_ManCoNum(pAig) );
    for ( i = 0; i < Aig_ManCoNum(pAig); i++ )
        Vec_IntPush( p->vPrefix, p->pCnfB->pVarNums[Aig_ManCo(pAig, i)->Id] );
    p->vImageBad = Vec_IntStart( p->pPars->fResetPrefix ? 1 : nFrames + 1 );
    Aig_ManStop( pAig );
finish:
    Gia_ManStop( pNew );
    Vec_IntFree( vState );
    Vec_IntFree( vOutputs );
    Vec_IntFree( vPis );
    Vec_IntFree( vResets );
    return p->pCnfB != NULL;
}

/**Function*************************************************************

  Synopsis    [Builds the bounded encoding for the selected search direction.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Imc_ManBuildSuffix( Imc_Man_t * p, int nFrames )
{
    p->nSuffixGeneration++;
    Vec_IntFreeP( &p->vSuffixClauses );
    Vec_IntFreeP( &p->vSuffixMap );
    if ( p->fExtendUnroll && p->pPred == NULL && (!p->pPars->fBackward || p->pPars->fResetPrefix) )
        return Imc_ManExtendSuffix( p, nFrames );
    if ( p->pPars->fBackward )
        return Imc_ManBuildPrefix( p, nFrames );
    return Imc_ManBuildSuffixFwd( p, nFrames );
}

// Reuse the normalized literals and variable map of an unchanged suffix.
// Fresh solvers still receive its clauses, but mapping and unit splitting
// are done once per depth instead of once per image query.
/**Function*************************************************************

  Synopsis    [Loads a forward suffix using its normalized clause cache.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_SatAddSuffixFwd( Imc_Sat_t * pSat, Imc_Man_t * p )
{
    int i, nLits, * pLit;
    Vec_Int_t * vLits;
    if ( p->vSuffixClauses && p->nCachedGeneration == p->nSuffixGeneration && pSat->nVars == p->nSuffixStart )
    {
        while ( pSat->nVars < p->nSuffixVars )
            Imc_SatNewVar( pSat, 0 );
        Vec_IntClear( pSat->vMap );
        Vec_IntAppend( pSat->vMap, p->vSuffixMap );
        for ( i = 0; i < Vec_IntSize(p->vSuffixClauses); i += nLits + 1 )
        {
            nLits = Vec_IntEntry( p->vSuffixClauses, i );
            Imc_SatAddClause( pSat, Vec_IntArray(p->vSuffixClauses) + i + 1, nLits, 0 );
        }
        return;
    }
    Vec_IntFreeP( &p->vSuffixClauses );
    Vec_IntFreeP( &p->vSuffixMap );
    pSat->vCapture = p->vSuffixClauses = Vec_IntAlloc( 1024 );
    p->nSuffixStart = pSat->nVars;
    p->nCachedGeneration = p->nSuffixGeneration;
    vLits = Vec_IntAlloc( 16 );
    for ( i = 0; i < p->pCnfB->nClauses; i++ )
    {
        Vec_IntClear( vLits );
        for ( pLit = p->pCnfB->pClauses[i]; pLit < p->pCnfB->pClauses[i+1]; pLit++ )
            Vec_IntPush( vLits, Abc_Var2Lit(Imc_SatVar(pSat, Vec_IntEntry(p->vMapB, Abc_Lit2Var(*pLit)), 0), Abc_LitIsCompl(*pLit)) );
        Imc_SatAddClause( pSat, Vec_IntArray(vLits), Vec_IntSize(vLits), 0 );
    }
    pSat->vCapture = NULL;
    p->nSuffixVars = pSat->nVars;
    p->vSuffixMap = Vec_IntDup( pSat->vMap );
    Vec_IntFree( vLits );
}

/**Function*************************************************************

  Synopsis    [Connects the backward image interface to the bounded prefix.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_SatConnectPrefix( Imc_Sat_t * pSat, Imc_Man_t * p, int nFrames )
{
    int i, f, Var, StateVar, Lits[3];
    if ( pSat->vShared == NULL )
        pSat->vShared = Vec_StrStart( Gia_ManRegNum(p->pGia) );
    if ( pSat->vLoaded == NULL )
        return;
    Vec_IntForEachEntry( p->vRos, Var, i )
    {
        if ( !Vec_StrEntry(pSat->vLoaded, Var) || Vec_StrEntry(pSat->vShared, i) )
            continue;
        Vec_StrWriteEntry( pSat->vShared, i, 1 );
        if ( p->pPars->fResetPrefix )
        {
            StateVar = Vec_IntEntry( p->vPrefix, i );
            Imc_SatLoadCnfCone( pSat, p->pCnfB, p->vCnfStartB, p->vCnfCountB, &pSat->vLoadedB, StateVar, p->pCnf->nVars, 0 );
            Lits[0] = Abc_Var2Lit( Imc_SatVar(pSat, Var, 1), 0 );
            Lits[1] = Abc_Var2Lit( Imc_SatVar(pSat, StateVar + p->pCnf->nVars, 0), 1 );
            Imc_SatAddClause( pSat, Lits, 2, 0 );
            Lits[0] ^= 1; Lits[1] ^= 1;
            Imc_SatAddClause( pSat, Lits, 2, 0 );
            continue;
        }
        for ( f = 0; f < nFrames; f++ )
        {
            StateVar = Vec_IntEntry( p->vPrefix, f * Gia_ManRegNum(p->pGia) + i );
            Imc_SatLoadCnfCone( pSat, p->pCnfB, p->vCnfStartB, p->vCnfCountB, &pSat->vLoadedB, StateVar, p->pCnf->nVars, 0 );
            Lits[0] = Abc_Var2Lit( Vec_IntEntry(p->vImageBad, f+1), 1 );
            Lits[1] = Abc_Var2Lit( Imc_SatVar(pSat, Var, 1), 0 );
            Lits[2] = Abc_Var2Lit( Imc_SatVar(pSat, StateVar + p->pCnf->nVars, 0), 1 );
            Imc_SatAddClause( pSat, Lits, 3, 0 );
            Lits[1] ^= 1; Lits[2] ^= 1;
            Imc_SatAddClause( pSat, Lits, 3, 0 );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Checks the bad output in the zero-initialized state.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Imc_ManCheckInitial( Imc_Man_t * p )
{
    Imc_Sat_t Sat;
    Vec_Int_t * vAss = Vec_IntAlloc( Gia_ManRegNum(p->pGia) + 1 );
    int i, Var, Status;
    memset(&Sat, 0, sizeof(Sat));
    Sat.pSat = sat_solver_new();
    Sat.nVars = p->pCnf->nVars;
    sat_solver_setnvars( Sat.pSat, Sat.nVars );
    Imc_SatAddCnf( &Sat, p->pCnf, 0, 0 );
    Vec_IntForEachEntry( p->vRos, Var, i )
        Vec_IntPush( vAss, Abc_Var2Lit(Var, 1) );
    Vec_IntPush( vAss, Abc_Var2Lit(p->iBad, 0) );
    sat_solver_set_runtime_limit( Sat.pSat, p->TimeStop );
    Status = Sat.fUnsat ? l_False : sat_solver_solve( Sat.pSat, Vec_IntArray(vAss), Vec_IntArray(vAss) + Vec_IntSize(vAss), p->pPars->nConfLimit, 0, 0, 0 );
    if ( Status == l_True )
    {
        p->pGia->pCexSeq = Imc_ManReadCex( p, Sat.pSat, NULL, NULL, NULL, 0, 0, 0, 1 );
        if ( p->pGia->pCexSeq == NULL )
            Status = l_Undef;
    }
    Vec_IntFree( vAss );
    sat_solver_delete( Sat.pSat );
    return Status;
}

/**Function*************************************************************

  Synopsis    [Initializes the incremental frontier containment or induction solver.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Imc_ManIndStart( Imc_Man_t * p )
{
    if ( p->Ind.pSat )
        sat_solver_delete( p->Ind.pSat );
    Vec_StrFreeP( &p->Ind.vLoaded );
    memset( &p->Ind, 0, sizeof(Imc_Sat_t) );
    p->Ind.pSat = sat_solver_new();
    p->Ind.nVars = p->pPars->fInductive ? p->pCnf->nVars : Gia_ManRegNum(p->pGia);
    Vec_IntFreeP( &p->vStates );
    p->vStates = Vec_IntStartNatural( Gia_ManRegNum(p->pGia) );
    sat_solver_setnvars( p->Ind.pSat, p->Ind.nVars );
    sat_solver_set_runtime_limit( p->Ind.pSat, p->TimeStop );
    p->iUnion = -1;
    p->fIndPending = 0;
}

/**Function*************************************************************

  Synopsis    [Computes the propagation allowance of a cooperative SAT query.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static ABC_INT64_T Imc_ManPropagationLimit( Imc_Man_t * p, int nVars )
{
    int fLinearAllowance = p->pPars->fBackward || (!p->iPredClass &&
        Gia_ManAndNum(p->pGia) >= 16384 && Gia_ManAndNum(p->pGia) < 65536);
    ABC_INT64_T Limit = (ABC_INT64_T)p->nQueryConfLimit * 256;
    // Replaying assumptions can propagate almost every variable before
    // search starts. Allow that work even in a small forward probe, or a
    // resumed query can exhaust the same budget without learning a clause.
    if ( !p->nQueryConfLimit ) return 0;
    return fLinearAllowance ? Limit + (ABC_INT64_T)nVars * 64 :
        (Limit > nVars ? Limit : nVars);
}

/**Function*************************************************************

  Synopsis    [Checks or resumes closure of the accumulated frontier union.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Imc_ManIndCheck( Imc_Man_t * p )
{
    int Lit0, Lit1, Lit, Status, i, Reg, Before, Limit = p->pPars->nConfLimit;
    abctime clk = Abc_Clock();
    word Visits;
    if ( p->nQueryConfLimit && (!Limit || p->nQueryConfLimit < Limit) )
        Limit = p->nQueryConfLimit;
    if ( !p->fIndPending )
    {
        if ( !p->pPars->fInductive )
            p->iIndQuery = Imc_SatAddFront( &p->Ind, p, p->vStates, 0 );
        else
        {
            Vec_IntForEachEntry( p->vFrontUsed, Reg, i )
                Imc_SatLoadCone( &p->Ind, p, Vec_IntEntry(p->vRis, Reg), 0 );
            Lit0 = Imc_SatAddFront( &p->Ind, p, p->pPars->fBackward ? p->vRis : p->vRos, 0 );
            Lit1 = Abc_LitNot( Imc_SatAddFront(&p->Ind, p, p->pPars->fBackward ? p->vRos : p->vRis, 0) );
            Imc_SatAddClause( &p->Ind, &Lit1, 1, 0 );
            if ( p->iUnion < 0 )
                p->iUnion = Lit0;
            else
            {
                Lit = Abc_Var2Lit( Imc_SatNewVar(&p->Ind, 0), 0 );
                Imc_SatAddAnd( &p->Ind, Abc_LitNot(Lit), Abc_LitNot(p->iUnion), Abc_LitNot(Lit0), 0 );
                p->iUnion = Lit;
            }
            p->iIndQuery = p->iUnion;
        }
    }
    Before = sat_solver_nconflicts( p->Ind.pSat );
    Visits = p->Ind.pSat->stats.inspects;
    sat_solver_set_runtime_limit( p->Ind.pSat, p->TimeStop );
    // A large formula needs a linear amount of propagation before its
    // conflict count is a useful measure of search work.
    Status = p->Ind.fUnsat ? l_False : sat_solver_solve(p->Ind.pSat,
        &p->iIndQuery, &p->iIndQuery + 1, Limit, Imc_ManPropagationLimit(p, sat_solver_nvars(p->Ind.pSat)), 0, 0);
    p->nConflicts += Abc_MaxInt(0, sat_solver_nconflicts(p->Ind.pSat) - Before);
    p->nSatVisits += (word)p->Ind.pSat->stats.inspects - Visits;
    p->fIndPending = Status == l_Undef && p->nQueryConfLimit &&
        (!p->TimeStop || Abc_Clock() < p->TimeStop);
    // Do not exclude a frontier until its containment query finishes.
    if ( Status != l_Undef && !p->pPars->fInductive )
    {
        Lit = p->iIndQuery ^ 1;
        Imc_SatAddClause( &p->Ind, &Lit, 1, 0 );
    }
    p->timeInd += Abc_Clock() - clk;
    return Status;
}

/**Function*************************************************************

  Synopsis    [Checks the image solver's global deadline.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_ManTerminate( void * pUser )
{
    Imc_Man_t * p = (Imc_Man_t *)pUser;
    return p->TimeStop && Abc_Clock() >= p->TimeStop;
}

/**Function*************************************************************

  Synopsis    [Encodes the composed predicate F(T(s, x)) in partition A.]

  Description [The current state remains the interpolation interface.
  Hashing and rewriting can simplify across the frontier/transition
  boundary before introducing any auxiliary SAT variables.]

  SideEffects [Marks the current-state inputs needed by the prefix.]

  SeeAlso     []

***********************************************************************/

// Incremental composition retains definitions of shared subgraphs. Only
// the frontier assertion is guarded, so learned clauses over transition
// nodes remain useful after the preceding image has been retired.
static int Imc_SatAddComposedCached( Imc_Sat_t * pSat, Imc_Man_t * p, Gia_Man_t * pFront )
{
    Gia_Man_t * pNew = pSat->pCompose;
    Gia_Obj_t * pObj;
    Vec_Int_t * vStack;
    int i, Id, Id0, Id1, Lit, Root, Key, Pair[2];
    if ( pNew == NULL )
    {
        pSat->pCompose = pNew = Gia_ManStart( Gia_ManObjNum(p->pGia) );
        pSat->vComposeNext = Vec_IntAlloc( Gia_ManRegNum(p->pGia) );
        pSat->vComposeVars = Vec_IntAlloc( Gia_ManObjNum(p->pGia) );
        Gia_ManHashStart( pNew );
        Gia_ManConst0(p->pGia)->Value = 0;
        Gia_ManForEachCi( p->pGia, pObj, i )
            pObj->Value = Gia_ManAppendCi( pNew );
        Gia_ManForEachAnd( p->pGia, pObj, i )
        {
            if ( (i & 1023) == 0 && Imc_ManTerminate(p) )
                return -1;
            pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        }
        Gia_ManForEachRi( p->pGia, pObj, i )
            Vec_IntPush( pSat->vComposeNext, Gia_ObjFanin0Copy(pObj) );
    }
    Gia_ManConst0(pFront)->Value = 0;
    Gia_ManForEachCi( pFront, pObj, i )
        pObj->Value = Vec_IntEntry( pSat->vComposeNext, i );
    Gia_ManForEachAnd( pFront, pObj, i )
    {
        if ( (i & 1023) == 0 && Imc_ManTerminate(p) )
            return -1;
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    }
    Root = Gia_ObjFanin0Copy( Gia_ManCo(pFront, 0) );
    Vec_IntFillExtra( pSat->vComposeVars, Gia_ManObjNum(pNew), -1 );
    if ( pSat->vLoaded == NULL )
        pSat->vLoaded = Vec_StrStart( p->pCnf->nVars );
    vStack = Vec_IntAlloc( 64 );
    Vec_IntPush( vStack, Abc_Lit2Var(Root) );
    while ( Vec_IntSize(vStack) )
    {
        Id = Vec_IntEntryLast( vStack );
        if ( Vec_IntEntry(pSat->vComposeVars, Id) >= 0 )
        {
            Vec_IntPop( vStack );
            continue;
        }
        if ( (Id & 1023) == 0 && Imc_ManTerminate(p) )
        {
            Vec_IntFree( vStack );
            return -1;
        }
        pObj = Gia_ManObj( pNew, Id );
        if ( Gia_ObjIsAnd(pObj) )
        {
            Id0 = Gia_ObjFaninId0p( pNew, pObj );
            Id1 = Gia_ObjFaninId1p( pNew, pObj );
            if ( Vec_IntEntry(pSat->vComposeVars, Id0) < 0 )
            {
                Vec_IntPush( vStack, Id0 );
                continue;
            }
            if ( Vec_IntEntry(pSat->vComposeVars, Id1) < 0 )
            {
                Vec_IntPush( vStack, Id1 );
                continue;
            }
            Lit = Abc_Var2Lit( Imc_SatNewVar(pSat, 1), 0 );
            Imc_SatAddAnd( pSat, Lit, Vec_IntEntry(pSat->vComposeVars, Id0) ^ Gia_ObjFaninC0(pObj),
                Vec_IntEntry(pSat->vComposeVars, Id1) ^ Gia_ObjFaninC1(pObj), 1 );
        }
        else if ( Gia_ObjIsCi(pObj) )
        {
            i = Gia_ObjCioId( pObj );
            Key = i < Gia_ManPiNum(p->pGia) ? Vec_IntEntry(p->vPis, i) : Vec_IntEntry(p->vRos, i - Gia_ManPiNum(p->pGia));
            Lit = Abc_Var2Lit( Imc_SatVar(pSat, Key, 1), 0 );
            Vec_StrWriteEntry( pSat->vLoaded, Key, 1 );
        }
        else
        {
            Lit = Abc_Var2Lit( Imc_SatNewVar(pSat, 1), 1 );
            Imc_SatAddClause( pSat, &Lit, 1, 1 );
            Lit ^= 1;
        }
        Vec_IntWriteEntry( pSat->vComposeVars, Id, Lit );
        Vec_IntPop( vStack );
    }
    Vec_IntFree( vStack );
    Pair[0] = Abc_Var2Lit( pSat->iGuard, 1 );
    Pair[1] = Vec_IntEntry(pSat->vComposeVars, Abc_Lit2Var(Root)) ^ Abc_LitIsCompl(Root);
    Imc_SatAddClause( pSat, Pair, 2, 1 );
    return Pair[0] ^ 1;
}

/**Function*************************************************************

  Synopsis    [Composes and simplifies a backward image before CNF encoding.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_SatAddComposed( Imc_Sat_t * pSat, Imc_Man_t * p, Gia_Man_t * pFront )
{
    Gia_Man_t * pNew = Gia_ManStart( Gia_ManObjNum(p->pGia) + Gia_ManObjNum(pFront) ), * pTemp;
    Gia_Obj_t * pObj;
    Aig_Man_t * pAig, * pRewr;
    Cnf_Dat_t * pCnf;
    Vec_Int_t * vMap, * vLits;
    Vec_Str_t * vUsed;
    int i, Var, Key, Lit, * pLit;
    pNew->fAddStrash = 1;
    Gia_ManHashStart( pNew );
    Gia_ManConst0(p->pGia)->Value = 0;
    Gia_ManForEachCi( p->pGia, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( p->pGia, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManConst0(pFront)->Value = 0;
    Gia_ManForEachCi( pFront, pObj, i )
        pObj->Value = Gia_ObjFanin0Copy( Gia_ManRi(p->pGia, i) );
    Gia_ManForEachAnd( pFront, pObj, i )
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(Gia_ManCo(pFront, 0)) );
    Gia_ManHashStop( pNew );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    pAig = Gia_ManToAigSimple( pNew );
    Gia_ManStop( pNew );
    pAig->Time2Quit = p->TimeStop;
    pRewr = Dar_ManRwsat( pAig, 1, 0 );
    Aig_ManStop( pAig );
    if ( pRewr == NULL )
        return -1;
    pCnf = Cnf_Derive( pRewr, 1 );
    vMap = Vec_IntStartFull( pCnf->nVars );
    vLits = Vec_IntAlloc( 16 );
    vUsed = Vec_StrStart( pCnf->nVars );
    for ( pLit = pCnf->pClauses[0]; pLit < pCnf->pClauses[pCnf->nClauses]; pLit++ )
        Vec_StrWriteEntry( vUsed, Abc_Lit2Var(*pLit), 1 );
    if ( pSat->vLoaded == NULL )
        pSat->vLoaded = Vec_StrStart( p->pCnf->nVars );
    for ( i = 0; i < Aig_ManCiNum(pRewr); i++ )
    {
        Var = pCnf->pVarNums[Aig_ManCi(pRewr, i)->Id];
        if ( !Vec_StrEntry(vUsed, Var) )
            continue;
        Key = i < Gia_ManPiNum(p->pGia) ? Vec_IntEntry(p->vPis, i) : Vec_IntEntry(p->vRos, i - Gia_ManPiNum(p->pGia));
        Vec_IntWriteEntry( vMap, Var, Imc_SatVar(pSat, Key, 1) );
        Vec_StrWriteEntry( pSat->vLoaded, Key, 1 );
    }
    for ( i = 0; i < pCnf->nClauses; i++ )
    {
        Vec_IntClear( vLits );
        for ( pLit = pCnf->pClauses[i]; pLit < pCnf->pClauses[i+1]; pLit++ )
        {
            Var = Abc_Lit2Var( *pLit );
            if ( Vec_IntEntry(vMap, Var) < 0 )
                Vec_IntWriteEntry( vMap, Var, Imc_SatNewVar(pSat, 1) );
            Vec_IntPush( vLits, Abc_Var2Lit(Vec_IntEntry(vMap, Var), Abc_LitIsCompl(*pLit)) );
        }
        if ( pSat->iGuard )
            Vec_IntPush( vLits, Abc_Var2Lit(pSat->iGuard, 1) );
        Imc_SatAddClause( pSat, Vec_IntArray(vLits), Vec_IntSize(vLits), 1 );
    }
    Lit = Abc_Var2Lit( Vec_IntEntry(vMap, pCnf->pVarNums[Aig_ManCo(pRewr, 0)->Id]), 0 );
    if ( pSat->iGuard )
    {
        int Pair[2] = { Abc_Var2Lit(pSat->iGuard, 1), Lit };
        Imc_SatAddClause( pSat, Pair, 2, 1 );
        Lit = Abc_Var2Lit( pSat->iGuard, 0 );
    }
    Vec_StrFree( vUsed );
    Vec_IntFree( vLits );
    Vec_IntFree( vMap );
    Cnf_DataFree( pCnf );
    Aig_ManStop( pRewr );
    return Lit;
}

/**Function*************************************************************

  Synopsis    [Releases the image solver, proof stream, and auxiliary encodings.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Imc_ManImageStop( Imc_Man_t * p )
{
    if ( p->Image.pSat2 )
        sat_solver2_delete( p->Image.pSat2 );
    if ( p->Image.pCad )
    {
        ccadical_close_proof( p->Image.pCad );
        ccadical_release( p->Image.pCad );
    }
    if ( p->Image.pProof )
        fclose( p->Image.pProof );
    if ( p->Image.pPrf )
        Imc_PrfStop( p->Image.pPrf );
    Vec_StrFreeP( &p->Image.vLoaded );
    Vec_StrFreeP( &p->Image.vLoadedB );
    Vec_StrFreeP( &p->Image.vShared );
    Vec_IntFreeP( &p->Image.vMap );
    Vec_IntFreeP( &p->Image.vComposeVars );
    Vec_IntFreeP( &p->Image.vComposeNext );
    Gia_ManStopP( &p->Image.pCompose );
    memset( &p->Image, 0, sizeof(Imc_Sat_t) );
}

/**Function*************************************************************

  Synopsis    [Connects predicate or register interfaces to the transition encoding.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_SatAddPredicates( Imc_Sat_t * pSat, Imc_Man_t * p, int fPartA, int fAbstract )
{
    Gia_Man_t * pPred = p->pPred;
    Gia_Obj_t * pObj;
    int i, Var, Lit, Pair[2], nRegs = Gia_ManCiNum(pPred);
    Lit = Abc_Var2Lit( Imc_SatNewVar(pSat, fPartA), 1 );
    Imc_SatAddClause( pSat, &Lit, 1, fPartA );
    Gia_ManConst0(pPred)->Value = Lit ^ 1;
    Gia_ManForEachCi( pPred, pObj, i )
    {
        Var = i + 1;
        if ( fAbstract )
        {
            int Key = fPartA ? Vec_IntEntry(p->pPars->fBackward ? p->vRos : p->vRis, i) : p->pCnf->nVars + Vec_IntEntry(p->vPrefix, i);
            Var = Imc_SatVar( pSat, Key, fPartA );
            if ( !fPartA && p->pPars->fBackward && Gia_ObjRefNum(pPred, pObj) )
                Imc_SatLoadCnfCone( pSat, p->pCnfB, p->vCnfStartB, p->vCnfCountB,
                    &pSat->vLoadedB, Key - p->pCnf->nVars, p->pCnf->nVars, 0 );
            if ( fPartA && !p->pPars->fBackward && Gia_ObjRefNum(pPred, pObj) )
                Imc_SatLoadCone( pSat, p, Key, 1 );
        }
        pObj->Value = Abc_Var2Lit( Var, 0 );
    }
    Gia_ManForEachAnd( pPred, pObj, i )
    {
        pObj->Value = Abc_Var2Lit( Imc_SatNewVar(pSat, fPartA), 0 );
        Imc_SatAddAnd( pSat, pObj->Value, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj), fPartA );
    }
    Gia_ManForEachCo( pPred, pObj, i )
    {
        Pair[0] = Abc_Var2Lit( (fAbstract ? 0 : nRegs) + i + 1, 1 );
        Pair[1] = Gia_ObjFanin0Copy( pObj );
        Imc_SatAddClause( pSat, Pair, 2, fPartA );
        Pair[0] ^= 1;
        Pair[1] ^= 1;
        Imc_SatAddClause( pSat, Pair, 2, fPartA );
    }
}

// Replay all inputs of an abstract model, retaining the concrete boundary
// even when its prefix cone was not needed by any current predicate.
/**Function*************************************************************

  Synopsis    [Simulates a trace concretely and returns its first verified violation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Cex_t * Imc_ManReplay( Imc_Man_t * p, Abc_Cex_t * pTrace, int Boundary, Vec_Str_t * vBoundary )
{
    Abc_Cex_t * pResult = NULL;
    Vec_Str_t * vState = Vec_StrStart( Gia_ManRegNum(p->pGia) );
    Gia_Obj_t * pObj;
    int f, i;
    for ( f = 0; f <= pTrace->iFrame; f++ )
    {
        if ( p->TimeStop && Abc_Clock() >= p->TimeStop )
            break;
        if ( f == Boundary )
            for ( i = 0; i < Vec_StrSize(vState); i++ )
                Vec_StrPush( vBoundary, Vec_StrEntry(vState, i) );
        Gia_ManConst0(p->pGia)->Value = 0;
        Gia_ManForEachPi( p->pGia, pObj, i )
            pObj->Value = Imc_CexHasBit( pTrace->pData, pTrace->nRegs + f * pTrace->nPis + i );
        Gia_ManForEachRo( p->pGia, pObj, i )
            pObj->Value = Vec_StrEntry( vState, i );
        Gia_ManForEachAnd( p->pGia, pObj, i )
            pObj->Value = (Gia_ObjFanin0(pObj)->Value ^ Gia_ObjFaninC0(pObj)) &
                         (Gia_ObjFanin1(pObj)->Value ^ Gia_ObjFaninC1(pObj));
        pObj = Gia_ManPo( p->pGia, 0 );
        if ( Gia_ObjFanin0(pObj)->Value ^ Gia_ObjFaninC0(pObj) )
        {
            pResult = Abc_CexAlloc( pTrace->nRegs, pTrace->nPis, f + 1 );
            pResult->iPo = 0;
            pResult->iFrame = f;
            for ( i = 0; i < pResult->nBits; i++ )
                if ( Imc_CexHasBit(pTrace->pData, i) )
                    Imc_CexSetBit( pResult->pData, i );
            if ( !Gia_ManVerifyCex(p->pGia, pResult, 0) )
                Abc_CexFreeP( &pResult );
            break;
        }
        Gia_ManForEachRi( p->pGia, pObj, i )
            Vec_StrWriteEntry( vState, i, Gia_ObjFanin0(pObj)->Value ^ Gia_ObjFaninC0(pObj) );
    }
    Vec_StrFree( vState );
    return pResult;
}

// Bound each batch as well as the accumulated vocabulary. Structural
// references rank genuine model mismatches; they never invent a mismatch.
/**Function*************************************************************

  Synopsis    [Exposes a bounded, ranked batch of mismatching registers.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Imc_ManRefinePredicates( Imc_Man_t * p, Vec_Str_t * vMismatch )
{
    Vec_Str_t * vExposed = Vec_StrStart( Gia_ManRegNum(p->pGia) );
    Vec_Wrd_t * vRanked = Vec_WrdAlloc( 16 );
    Vec_Int_t * vRefs = Vec_IntStart( Gia_ManObjNum(p->pGia) );
    Gia_Obj_t * pObj, * pDriver;
    Gia_Man_t * pNew;
    int i, k, Reg, nAdded, Limit = Abc_MinInt(64 - p->nRefinements, IMC_PRED_MAX - Gia_ManCoNum(p->pPred));
    if ( Limit <= 0 || (p->TimeStop && Abc_Clock() >= p->TimeStop) )
        goto finish;
    Gia_ManForEachCo( p->pPred, pObj, i )
    {
        pDriver = Gia_ObjFanin0( pObj );
        if ( Gia_ObjIsCi(pDriver) )
            Vec_StrWriteEntry( vExposed, Gia_ObjCioId(pDriver), 1 );
    }
    Gia_ManForEachAnd( p->pGia, pObj, i )
    {
        Vec_IntAddToEntry( vRefs, Gia_ObjFaninId0p(p->pGia, pObj), 1 );
        Vec_IntAddToEntry( vRefs, Gia_ObjFaninId1p(p->pGia, pObj), 1 );
    }
    Gia_ManForEachCo( p->pGia, pObj, i )
        Vec_IntAddToEntry( vRefs, Gia_ObjFaninId0p(p->pGia, pObj), 1 );
    Gia_ManForEachRo( p->pGia, pObj, i )
        if ( !Vec_StrEntry(vExposed, i) && Vec_StrEntry(vMismatch, i) )
            Vec_WrdPush( vRanked, ((word)(0x7fffffff - Vec_IntEntry(vRefs, Gia_ObjId(p->pGia, pObj))) << 32) | (unsigned)i );
    Vec_WrdSort( vRanked, 0 );
    nAdded = Abc_MinInt( Limit, Vec_WrdSize(vRanked) );
    if ( nAdded == 0 )
        goto finish;
    pNew = Gia_ManStart( Gia_ManObjNum(p->pPred) + nAdded );
    Gia_ManConst0(p->pPred)->Value = 0;
    Gia_ManForEachCi( p->pPred, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( p->pPred, pObj, i )
        pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachCo( p->pPred, pObj, i )
    {
        // Preserve the Base/Full output contract through refinement.
        if ( i == Gia_ManCoNum(p->pPred) - 2 )
            for ( k = 0; k < nAdded; k++ )
            {
                Reg = (int)(unsigned)Vec_WrdEntry( vRanked, k );
                Gia_ManAppendCo( pNew, Gia_Obj2Lit(pNew, Gia_ManCi(pNew, Reg)) );
            }
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    }
    Gia_ManCreateRefs( pNew );
    Gia_ManStop( p->pPred );
    p->pPred = pNew;
    p->fRefined = 1;
    p->nRefinements += nAdded;
    if ( p->pPars->fVerbose )
        Abc_Print( 1, "IMC: Refining predicate abstraction with %d registers (%d total).\n", nAdded, p->nRefinements );
finish:
    Vec_StrFree( vExposed );
    Vec_WrdFree( vRanked );
    Vec_IntFree( vRefs );
}

/**Function*************************************************************

  Synopsis    [Finds constrained model mismatches for predicate refinement.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_SatRefinePredicates( Imc_Sat_t * pSat, Imc_Man_t * p, Vec_Str_t * vBoundary )
{
    Vec_Str_t * vMismatch = Vec_StrStart( Gia_ManRegNum(p->pGia) );
    Vec_Str_t * vUsed = NULL;
    int i, Key, Var, Value;
    if ( Vec_StrSize(vBoundary) != Gia_ManRegNum(p->pGia) )
        goto finish;
    if ( !p->pPars->fBackward )
    {
        vUsed = Vec_StrStart( Gia_ManRegNum(p->pGia) );
        Vec_IntForEachEntry( p->vSharedUsed, Var, i )
            Vec_StrWriteEntry( vUsed, Var, 1 );
    }
    for ( i = 0; i < Gia_ManRegNum(p->pGia); i++ )
    {
        if ( p->pPars->fBackward )
        {
            Key = Vec_IntEntry( p->vRos, i );
            if ( !pSat->vLoaded || !Vec_StrEntry(pSat->vLoaded, Key) )
                continue;
        }
        else
        {
            Key = p->pCnf->nVars + Vec_IntEntry( p->vPrefix, i );
            if ( !Vec_StrEntry(vUsed, i) )
                continue;
        }
        Var = Vec_IntEntry( pSat->vMap, Key );
        if ( Var < 0 )
            continue;
        Value = pSat->pCad ? ccadical_val(pSat->pCad, Var + 1) > 0 : sat_solver2_var_value(pSat->pSat2, Var);
        Vec_StrWriteEntry( vMismatch, i, Value != Vec_StrEntry(vBoundary, i) );
    }
    Imc_ManRefinePredicates( p, vMismatch );
finish:
    Vec_StrFreeP( &vUsed );
    Vec_StrFree( vMismatch );
}

/**Function*************************************************************

  Synopsis    [Computes or resumes an interpolated image and handles concrete counterexamples.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Imc_ManImage( Imc_Man_t * p, Gia_Man_t * pFront, int nFrames, int fInitial, int * pStatus )
{
    Imc_Sat_t Sat;
    Gia_Man_t * pImage = NULL;
    int fAbstract = p->pPars->fAbstract && (!p->pPars->fBackward || p->pPars->fResetPrefix) && p->pPred;
    Vec_Int_t * vLits = Vec_IntAlloc( 32 );
    Vec_Int_t * vGlobals = p->pPars->fBackward ? p->vRos : p->vRis;
    Vec_Int_t * vGlobalVars = Vec_IntStartNatural( (fAbstract ? 0 : Vec_IntSize(vGlobals)) + (p->pPred ? Gia_ManCoNum(p->pPred) : 0) );
    FILE * pProof = NULL;
    int i, f, Var, Lits[2], fReuse, fKeep, Before, Limit = p->pPars->nConfLimit;
    int fIncremental = p->pPars->fIncremental && !p->pPars->fUseMiniSat;
    abctime clk;
    word Visits = 0;
    // sat_solver2's resolution logger reserves variable zero.
    Vec_IntForEachEntry( vGlobalVars, Var, i )
        Vec_IntWriteEntry( vGlobalVars, i, Var + 1 );
    // MiniSat and incremental CaDiCaL retain learned clauses between
    // frontiers. Default LRAT queries use a fresh solver. Large MiniSat
    // suffixes benefit from retaining the solver for more image queries.
    if ( !p->Image.fPending && (p->nImageCalls++ & (p->pPars->fUseMiniSat && p->pCnfB->nClauses >= 131072 ? 31 : 7)) == 0 )
        Imc_ManImageStop( p );
    Sat = p->Image;
    pProof = Sat.pProof;
    if ( Sat.fPending )
    {
        Lits[0] = Sat.Query[0];
        Lits[1] = Sat.Query[1];
        goto solve;
    }
    fReuse = Sat.pSat2 != NULL || Sat.pCad != NULL;
    if ( fReuse && fIncremental )
        Imc_PrfAssertGlobals( Sat.pPrf, vGlobalVars );
    if ( !fReuse )
    {
        Sat.nVars = Vec_IntSize(vGlobalVars) + 1;
        Sat.vMap = Vec_IntStartFull( p->pCnf->nVars + p->pCnfB->nVars );
        if ( !fAbstract )
            Vec_IntForEachEntry( vGlobals, Var, i )
                Vec_IntWriteEntry( Sat.vMap, Var, i + 1 );
        Sat.fDual = p->pPars->fDual;
        Sat.pPrf = Imc_PrfStart( vGlobalVars, 0, Sat.nVars, Sat.fDual, p->pPars->fPudlak && !p->pPars->fUseMiniSat, fIncremental );
        *pStatus = l_Undef;
        if ( p->pPars->fUseMiniSat )
        {
            Sat.pSat2 = sat_solver2_new();
            sat_solver2_setnvars( Sat.pSat2, Sat.nVars );
            Sat.pSat2->pPrf1 = Vec_SetAlloc( 20 );
        }
        else
        {
            const char * pPlain[] = { "block", "compact", "condition", "congruence", "cover", "decompose", "deduplicate", "eagersubsume", "elim", "factor", "factorunbump", "fastelim", "flush", "inprobing", "inprocessing", "instantiate", "preprocesslight", "probe", "subsume", "sweep", "ternary", "transred", "vivify", "vivifydemote", "lucky", "walk", "stabilize", "chrono", "phase", NULL };
            pProof = Imc_ProofFile();
            if ( pProof == NULL )
            {
                Abc_Print( -1, "IMC: Cannot open a temporary proof stream.\n" );
                goto cleanup;
            }
            Sat.pCad = ccadical_init();
            if ( !p->pPars->fPreprocess || !fInitial )
                for ( i = 0; pPlain[i]; i++ )
                    ccadical_set_option( Sat.pCad, pPlain[i], 0 );
            ccadical_set_option( Sat.pCad, "quiet", 1 );
            ccadical_set_option( Sat.pCad, fIncremental ? "lidrup" : "lrat", 1 );
            ccadical_set_option( Sat.pCad, "binary", 1 );
            ccadical_set_option( Sat.pCad, "factor", 0 );
            ccadical_set_option( Sat.pCad, "condition", 0 );
            ccadical_set_option( Sat.pCad, "congruence", 0 );
            if ( !ccadical_trace_proof(Sat.pCad, pProof, fIncremental ? "imc-lidrup" : "imc-lrat") )
                goto cleanup;
            if ( fIncremental )
                Sat.pProof = pProof;
            ccadical_resize( Sat.pCad, Sat.nVars );
            ccadical_set_terminate( Sat.pCad, p, Imc_ManTerminate );
            if ( p->pPars->nConfLimit )
                ccadical_limit( Sat.pCad, "conflicts", p->pPars->nConfLimit );
        }
        // The image transition and frontier belong to A. The selected
        // state boundary is shared; all other variables are local.
        if ( Sat.pSat2 )
        {
            for ( i = 0; i < Sat.nVars; i++ )
                var_set_partA( Sat.pSat2, i, 0 );
        }
        if ( p->pPred )
        {
            Gia_Obj_t * pObj;
            Imc_SatAddPredicates( &Sat, p, 1, fAbstract );
            Imc_SatAddPredicates( &Sat, p, 0, fAbstract );
            if ( !fAbstract )
                Gia_ManForEachCi( p->pPred, pObj, i )
                    if ( Gia_ObjRefNum(p->pPred, pObj) )
                        Imc_SatLoadCone( &Sat, p, Vec_IntEntry(vGlobals, i), 1 );
        }
        if ( p->pPars->fBackward )
        {
            Var = Imc_SatNewVar( &Sat, 0 );
            Vec_IntWriteEntry( p->vImageBad, 0, Var );
            Vec_IntPush( vLits, Abc_Var2Lit(Var, !p->pPars->fResetPrefix) );
            for ( f = 1; !p->pPars->fResetPrefix && f <= nFrames; f++ )
            {
                Var = Imc_SatNewVar( &Sat, 0 );
                Vec_IntWriteEntry( p->vImageBad, f, Var );
                Vec_IntPush( vLits, Abc_Var2Lit(Var, 0) );
            }
            Imc_SatAddClause( &Sat, Vec_IntArray(vLits), Vec_IntSize(vLits), 0 );
        }
        else
            Imc_SatAddSuffixFwd( &Sat, p );
    }
    else
        Imc_PrfRestart( Sat.pPrf );
    *pStatus = l_Undef;
    if ( fIncremental )
    {
        // Retire the previous frontier's clauses while retaining shared
        // transition/prefix clauses and their unconditional consequences.
        if ( Sat.iGuard )
        {
            int Lit = Abc_Var2Lit( Sat.iGuard, 1 );
            Imc_SatAddClause( &Sat, &Lit, 1, 1 );
        }
        Sat.iGuard = Imc_SatNewVar( &Sat, 1 );
    }
    if ( p->pPars->fBackward && p->pPars->fCompose )
    {
        Lits[0] = fIncremental ? Imc_SatAddComposedCached(&Sat, p, pFront) : Imc_SatAddComposed(&Sat, p, pFront);
        if ( Lits[0] < 0 )
            goto cleanup;
    }
    else
    {
        Vec_IntForEachEntry( p->pPars->fBackward ? p->vFrontUsed : p->vSharedUsed, Var, i )
            Imc_SatLoadCone( &Sat, p, Vec_IntEntry(p->vRis, Var), 1 );
    }
    if ( p->pPars->fBackward && !fAbstract )
        Imc_SatConnectPrefix( &Sat, p, nFrames );
    if ( !p->pPars->fBackward || !p->pPars->fCompose )
        Lits[0] = Imc_SatAddFront( &Sat, p, p->pPars->fBackward ? p->vRis : p->vRos, 1 );
    // Include bad in every suffix frame, as in the complete version of
    // McMillan's algorithm, including systems that are not stuttering.
    Lits[1] = Abc_Var2Lit( p->pPars->fBackward ? Vec_IntEntry(p->vImageBad, 0) : Imc_SatVar(&Sat, Vec_IntEntry(p->vImageBad, 0), 0), 0 );
    if ( Sat.pCad && !fIncremental )
    {
        Imc_SatAddClause( &Sat, Lits, 1, 1 );
        Imc_SatAddClause( &Sat, Lits + 1, 1, 0 );
    }
solve:
    if ( p->nQueryConfLimit && (!Limit || p->nQueryConfLimit < Limit) )
        Limit = p->nQueryConfLimit;
    Before = Sat.pCad ? ccadical_conflicts(Sat.pCad) : sat_solver2_nconflicts(Sat.pSat2);
    clk = Abc_Clock();
    if ( Sat.pCad )
    {
        int Status;
        if ( fIncremental )
            for ( i = 0; i < 2; i++ )
                ccadical_assume( Sat.pCad, (Abc_Lit2Var(Lits[i])+1) * (Abc_LitIsCompl(Lits[i]) ? -1 : 1) );
        ccadical_limit( Sat.pCad, "conflicts", Limit ? Limit : -1 );
        // Preprocessing can do substantial work without a search conflict.
        // Bound deterministic polling work as well, and resume the same query.
        ccadical_limit( Sat.pCad, "terminate", p->nQueryConfLimit ?
            (int)Abc_MinWord(0x7fffffff, 4096 + 16 * (word)p->nQueryConfLimit) : 0 );
        Status = ccadical_solve( Sat.pCad );
        *pStatus = Status == 10 ? l_True : Status == 20 ? l_False : l_Undef;
        if ( fIncremental && Status == 20 )
            ccadical_conclude( Sat.pCad );
        if ( !fIncremental && Status != 0 )
            ccadical_close_proof( Sat.pCad );
        if ( fflush(pProof) || ferror(pProof) )
        {
            Abc_Print( -1, "IMC: Temporary proof stream write failed.\n" );
            Sat.fPending = 0;
            *pStatus = l_Undef;
            goto cleanup;
        }
    }
    else
    {
        sat_solver2_set_runtime_limit( Sat.pSat2, p->TimeStop );
        Visits = Sat.pSat2->stats.inspects;
        *pStatus = sat_solver2_solve( Sat.pSat2, Lits, Lits + 2, Limit,
            Imc_ManPropagationLimit(p, Sat.nVars), 0, 0 );
        p->nSatVisits += (word)Sat.pSat2->stats.inspects - Visits;
    }
    p->timeSat += Abc_Clock() - clk;
    p->nConflicts += Abc_MaxInt(0, (Sat.pCad ? ccadical_conflicts(Sat.pCad) : sat_solver2_nconflicts(Sat.pSat2)) - Before);
    if ( p->pPars->fVerbose && Sat.pSat2 )
        Abc_Print( 1, "IMC: MiniSat image %s; variables = %d; conflicts = %d; visits = %llu.\n",
            *pStatus == l_True ? "SAT" : *pStatus == l_False ? "UNSAT" : "paused",
            Sat.nVars, sat_solver2_nconflicts(Sat.pSat2) - Before,
            (unsigned long long)((word)Sat.pSat2->stats.inspects - Visits) );
    Sat.fPending = *pStatus == l_Undef && p->nQueryConfLimit &&
        (!p->TimeStop || Abc_Clock() < p->TimeStop);
    Sat.Query[0] = Lits[0];
    Sat.Query[1] = Lits[1];
    if ( *pStatus == l_False )
    {
        clk = Abc_Clock();
        if ( Sat.pSat2 )
            pImage = Imc_PrfReadSat( Sat.pPrf, Sat.pSat2, p->TimeStop );
        else if ( fIncremental )
            pImage = Imc_PrfReadIncremental( Sat.pPrf, pProof, Sat.nVars, Lits[0], Lits[1], p->TimeStop );
        else
            pImage = Imc_PrfRead( Sat.pPrf, pProof, Sat.nVars, p->pPars->fAutoItp, p->pPars->fMinimize, p->TimeStop );
        if ( !pImage && p->pPars->fVerbose )
            Abc_Print( 1, "IMC: UNSAT query produced no interpolant; proof bytes = %lld; stream error = %d.\n", (long long)(pProof ? Imc_ProofTell(pProof) : 0), pProof ? ferror(pProof) : 0 );
        if ( pImage && p->pPars->fVerbose && Imc_PrfWasMinimized(Sat.pPrf) )
            Abc_Print( 1, "IMC: Selected a smaller interpolant from the minimized proof core.\n" );
        if ( pImage )
        {
            Aig_Man_t * pAig, * pTemp;
            Gia_Man_t * pBdd;
            p->nItpNodes += Gia_ManAndNum(pImage);
            pBdd = Imc_ManRewriteBdd( pImage, p->pPars->nBddMax, p->TimeStop );
            if ( pBdd )
            {
                Gia_ManStop( pImage );
                pImage = pBdd;
            }
            pAig = Gia_ManToAigSimple( pImage );
            Gia_ManStop( pImage );
            pAig->Time2Quit = p->TimeStop;
            pTemp = Dar_ManRwsat( pAig, 1, 0 );
            pImage = pTemp ? Gia_ManFromAigSimple(pTemp) : NULL;
            Aig_ManStop( pAig );
            if ( pTemp )
                Aig_ManStop( pTemp );
        }
        if ( pImage && p->pPars->fSweep && Gia_ManAndNum(pImage) > 256 )
        {
            Gia_Man_t * pSwept = Imc_ManRewriteSat( pImage, p->TimeStop );
            if ( pSwept )
            {
                Gia_ManStop( pImage );
                pImage = pSwept;
            }
        }
        if ( pImage && p->pPars->fWeaken )
        {
            Gia_Man_t * pWeak = Imc_PrfWeaken( Sat.pPrf, pImage, vGlobalVars, Sat.nVars, Lits[1], p->TimeStop );
            if ( pWeak )
            {
                if ( p->pPars->fVerbose )
                    Abc_Print( 1, "IMC: Weakened interpolant from %d to %d ANDs.\n", Gia_ManAndNum(pImage), Gia_ManAndNum(pWeak) );
                Gia_ManStop( pImage );
                pImage = pWeak;
            }
        }
        p->timeItp += Abc_Clock() - clk;
        if ( pImage && p->pPars->fCheck && Imc_PrfCheck(Sat.pPrf, pImage, vGlobalVars, Sat.nVars, Lits[0], Lits[1], p->pPars->nConfLimit, p->TimeStop) != 1 )
            Gia_ManStopP( &pImage );
        if ( pImage && p->pPred )
        {
            Gia_Man_t * pTemp = Imc_ManExpandPredicates( pImage, p->pPred );
            Gia_ManStop( pImage );
            pImage = pTemp;
        }
        if ( pImage == NULL )
            *pStatus = l_Undef;
    }
    else if ( *pStatus == l_True && fInitial )
    {
        int iStart = 0;
        // An abstract SAT model can already be a concrete trace. Replay it
        // on the original transition system before spending any refinement.
        if ( p->pPars->fBackward && p->pPars->fResetPrefix )
        {
            Vec_IntForEachEntry( p->vResets, Var, i )
            {
                Var = Vec_IntEntry( Sat.vMap, Var );
                if ( Var >= 0 && (Sat.pCad ? ccadical_val(Sat.pCad, Var + 1) > 0 : sat_solver2_var_value(Sat.pSat2, Var)) )
                    iStart = i + 1;
            }
            f = nFrames;
        }
        else for ( f = 1; f <= nFrames; f++ )
        {
            Var = Vec_IntEntry( p->vImageBad, f );
            if ( !p->pPars->fBackward )
                Var = Vec_IntEntry( Sat.vMap, Var );
            if ( Var >= 0 && (Sat.pCad ? ccadical_val(Sat.pCad, Var + 1) > 0 : sat_solver2_var_value(Sat.pSat2, Var)) )
                break;
        }
        if ( fAbstract )
        {
            Vec_Str_t * vBoundary = Vec_StrAlloc( Gia_ManRegNum(p->pGia) );
            Abc_Cex_t * pTrace = Imc_ManReadCex( p, NULL, Sat.pSat2, Sat.pCad, Sat.vMap, nFrames, iStart, 1, 0 );
            p->pGia->pCexSeq = Imc_ManReplay( p, pTrace, (p->pPars->fBackward ? nFrames - 1 : 1) - iStart, vBoundary );
            Abc_CexFree( pTrace );
            if ( p->pGia->pCexSeq == NULL )
                Imc_SatRefinePredicates( &Sat, p, vBoundary );
            Vec_StrFree( vBoundary );
        }
        else if ( f <= nFrames )
            p->pGia->pCexSeq = Imc_ManReadCex( p, NULL, Sat.pSat2, Sat.pCad, Sat.vMap, f, iStart, 0, 1 );
        if ( p->pGia->pCexSeq == NULL )
        {
            *pStatus = l_Undef;
        }
        else
            p->pPars->iFrame = p->pGia->pCexSeq->iFrame;
    }
cleanup:
    Vec_IntFree( vLits );
    Vec_IntFree( vGlobalVars );
    // A suspended query retains its exact assumptions, solver and unfinished
    // proof. Only a completed UNSAT query may advance to another frontier.
    fKeep = Sat.fPending || (*pStatus == l_False && pImage && (Sat.pSat2 || fIncremental));
    p->Image = Sat;
    p->Image.pProof = pProof;
    if ( !fKeep )
        Imc_ManImageStop( p );
    return pImage;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
