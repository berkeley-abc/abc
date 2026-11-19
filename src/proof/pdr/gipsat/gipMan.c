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
#include "base/main/main.h"

ABC_NAMESPACE_IMPL_START

#if ABC_HAS_THREAD_LOCAL
static ABC_THREAD_LOCAL Gip_Options_t * s_pGipOptions;
#endif

/**Function*************************************************************

  Synopsis    [Resolves a solver setting in the current frame's option scopes.]

  Description []

***********************************************************************/
const char * Gip_OptionGet( const char * pName )
{
#if ABC_HAS_THREAD_LOCAL
    Gip_Options_t * p;
    Abc_Frame_t * pFrame = s_pGipOptions ? Abc_FrameReadGlobalFrame() : NULL;
    int i;
    for ( p = s_pGipOptions; p; p = p->pPrevious )
    {
        if ( p->pFrame != pFrame ) continue;
        for ( i = 0; i < p->nOptions; i++ )
            if ( !strcmp(pName, p->pKeys[i]) ) return p->pValues[i];
        // Retain explicitly requested diagnostic checks in an isolated stage.
        if ( p->fIsolate && !strncmp(pName, "PDR2_", 5) && !strstr(pName, "_CHECK") )
            return NULL;
    }
#endif
    return getenv(pName);
}

/**Function*************************************************************

  Synopsis    [Enters a borrowed option scope on the calling thread.]

  Description []

***********************************************************************/
void Gip_OptionsPush( Gip_Options_t * p )
{
#if ABC_HAS_THREAD_LOCAL
    p->pFrame = Abc_FrameReadGlobalFrame();
    p->pPrevious = s_pGipOptions;
    s_pGipOptions = p;
#else
    (void)p;
#endif
}

/**Function*************************************************************

  Synopsis    [Restores the preceding option scope.]

  Description []

***********************************************************************/
void Gip_OptionsPop( Gip_Options_t * p )
{
#if ABC_HAS_THREAD_LOCAL
    assert(s_pGipOptions == p);
    s_pGipOptions = p->pPrevious;
#else
    (void)p;
#endif
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Collects the fanin literals and identifies the Boolean gate to encode.]

  Description []

***********************************************************************/
static int Gip_CnfStructuralInputs( Aig_Obj_t * pObj, int Mode, int * pLits )
{
    Aig_Obj_t * a, * b, * c;
    if ( Aig_ObjIsCo(pObj) || Aig_ObjIsBuf(pObj) )
    {
        pLits[0] = Aig_ObjToLit( Aig_ObjChild0(pObj) );
        return 1;
    }
    if ( !Aig_ObjIsNode(pObj) ) return 0;
    if ( (Mode == 1 || Aig_ObjIsExor(pObj)) && Aig_ObjRecognizeExor(pObj, &a, &b) )
    {
        pLits[0] = Aig_ObjToLit(a);
        pLits[1] = Aig_ObjToLit(b);
        return 3;
    }
    if ( Mode == 1 && Aig_ObjIsMuxType(pObj) )
    {
        c = Aig_ObjRecognizeMux( pObj, &a, &b );
        pLits[0] = Aig_ObjToLit(c);
        pLits[1] = Aig_ObjToLit(a);
        pLits[2] = Aig_ObjToLit(b);
        return 4;
    }
    pLits[0] = Aig_ObjToLit( Aig_ObjChild0(pObj) );
    pLits[1] = Aig_ObjToLit( Aig_ObjChild1(pObj) );
    return 2;
}

/**Function*************************************************************

  Synopsis    [Emits one defining clause into the structural CNF.]

  Description []

***********************************************************************/
static void Gip_CnfStructuralClause( Vec_Int_t * vData, Vec_Int_t * vOffsets, int * pLits, int nLits )
{
    Vec_IntPush( vOffsets, Vec_IntSize(vData) );
    Vec_IntPushArray( vData, pLits, nLits );
}

/**Function*************************************************************

  Synopsis    [Builds a gate-level CNF and its per-object clause ranges.]

  Description []

***********************************************************************/
// An alternative to the area-mapped CNF: direct AND/XOR/ITE definitions,
// retaining only referenced nodes. Each object's complete defining relation
// stays contiguous, preserving the dependency and lazy-loading interfaces.
static Cnf_Dat_t * Gip_CnfStructural( Aig_Man_t * pAig, int Mode )
{
    Cnf_Dat_t * pCnf = ABC_CALLOC( Cnf_Dat_t, 1 );
    Vec_Int_t * vData = Vec_IntAlloc( 1000 ), * vOffsets = Vec_IntAlloc( 1000 );
    int nObjs = Aig_ManObjNumMax(pAig), i, j, Kind, In[3], Out, nIn;
    char * pNeed = ABC_CALLOC( char, nObjs );
    Aig_Obj_t * pObj;
    Aig_ManForEachCo( pAig, pObj, i ) pNeed[Aig_ObjId(pObj)] = 1;
    pNeed[Aig_ObjId(Aig_ManConst1(pAig))] = 1;
    Aig_ManForEachObjReverse( pAig, pObj, i )
        if ( pNeed[i] )
        {
            Kind = Gip_CnfStructuralInputs( pObj, Mode, In );
            nIn = Kind == 4 ? 3 : Kind >= 2 ? 2 : Kind;
            for ( j = 0; j < nIn; j++ ) pNeed[Abc_Lit2Var(In[j])] = 1;
        }
    pCnf->pMan = pAig;
    pCnf->nVars = nObjs;
    pCnf->pObj2Clause = ABC_ALLOC( int, nObjs );
    pCnf->pObj2Count = ABC_CALLOC( int, nObjs );
    for ( i = 0; i < nObjs; i++ ) pCnf->pObj2Clause[i] = -1;
    Aig_ManForEachObj( pAig, pObj, i )
        if ( pNeed[i] )
        {
            pCnf->pObj2Clause[i] = Vec_IntSize( vOffsets );
            Out = Abc_Var2Lit( i, 0 );
            Kind = Gip_CnfStructuralInputs( pObj, Mode, In );
            if ( Aig_ObjIsConst1(pObj) )
                Gip_CnfStructuralClause( vData, vOffsets, &Out, 1 );
            else if ( Kind == 1 )
            {
                int a[2] = { Out, In[0]^1 }, b[2] = { Out^1, In[0] };
                Gip_CnfStructuralClause( vData, vOffsets, a, 2 );
                Gip_CnfStructuralClause( vData, vOffsets, b, 2 );
            }
            else if ( Kind == 2 )
            {
                int a[2] = { Out^1, In[0] }, b[2] = { Out^1, In[1] };
                int c[3] = { Out, In[0]^1, In[1]^1 };
                Gip_CnfStructuralClause( vData, vOffsets, a, 2 );
                Gip_CnfStructuralClause( vData, vOffsets, b, 2 );
                Gip_CnfStructuralClause( vData, vOffsets, c, 3 );
            }
            else if ( Kind == 3 )
            {
                int Clauses[4][3] = {{In[0]^1, In[1], Out}, {In[0], In[1]^1, Out},
                                    {In[0], In[1], Out^1}, {In[0]^1, In[1]^1, Out^1}};
                for ( j = 0; j < 4; j++ ) Gip_CnfStructuralClause( vData, vOffsets, Clauses[j], 3 );
            }
            else if ( Kind == 4 )
            {
                int Clauses[4][3] = {{In[1], In[0]^1, Out^1}, {In[1]^1, In[0]^1, Out},
                                    {In[2], In[0], Out^1}, {In[2]^1, In[0], Out}};
                for ( j = 0; j < 4; j++ ) Gip_CnfStructuralClause( vData, vOffsets, Clauses[j], 3 );
            }
            pCnf->pObj2Count[i] = Vec_IntSize(vOffsets) - pCnf->pObj2Clause[i];
        }
    pCnf->nLiterals = Vec_IntSize( vData );
    pCnf->nClauses = Vec_IntSize( vOffsets );
    Vec_IntPush( vOffsets, Vec_IntSize(vData) );
    pCnf->pClauses = ABC_ALLOC( int *, pCnf->nClauses + 1 );
    pCnf->pClauses[0] = ABC_ALLOC( int, pCnf->nLiterals );
    memcpy( pCnf->pClauses[0], Vec_IntArray(vData), sizeof(int) * pCnf->nLiterals );
    for ( i = 1; i <= pCnf->nClauses; i++ ) pCnf->pClauses[i] = pCnf->pClauses[0] + Vec_IntEntry(vOffsets, i);
    Vec_IntFree( vData );
    Vec_IntFree( vOffsets );
    ABC_FREE( pNeed );
    return pCnf;
}

/**Function*************************************************************

  Synopsis    [Exhaustively compares a small context's SAT encoding with AIG evaluation.]

  Description []

***********************************************************************/
// On small circuits, independently compare every CI assignment and every CO
// polarity against ordinary AIG evaluation. This checks the CNF itself, before
// a PDR trajectory can hide an encoding mistake behind an unused cone.
static void Gip_CtxCheckTruth( Gip_Ctx_t * p )
{
    Aig_Man_t * pAig = p->pAig;
    Aig_Obj_t * pObj;
    Gip_Solver_t * pSat;
    Vec_Int_t * vAssump;
    char * pVals;
    int nCis = Aig_ManCiNum(pAig), nAssumedCis, Mask, i, j, Lit, Ret, a, b;
    if ( nCis > 8 ) return;
    pSat = Gip_SolverNew( p );
    vAssump = Vec_IntAlloc( nCis + Aig_ManCoNum(pAig) );
    pVals = ABC_CALLOC( char, Aig_ManObjNumMax(pAig) );
    pVals[Aig_ObjId(Aig_ManConst1(pAig))] = 1;
    for ( Mask = 0; Mask < (1 << nCis); Mask++ )
    {
        Vec_IntClear( vAssump );
        Aig_ManForEachCi( pAig, pObj, i )
        {
            pVals[Aig_ObjId(pObj)] = (Mask >> i) & 1;
            // The unused-PI alias represents an arbitrary extension to the
            // original interface, not equality of independently supplied PI
            // values. Enumerate every original assignment, but project these
            // unobservable values out of the SAT assumptions.
            if ( Gip_CtxObjVar(p, pObj) == p->iUnusedPiVar )
            {
                assert( i < nCis - Aig_ManRegNum(pAig) && Aig_ObjRefs(pObj) == 0 );
                continue;
            }
            Vec_IntPush( vAssump, Abc_Var2Lit(Gip_CtxObjVar(p, pObj), !pVals[Aig_ObjId(pObj)]) );
        }
        nAssumedCis = Vec_IntSize(vAssump);
        Aig_ManForEachObj( pAig, pObj, i )
        {
            if ( Aig_ObjIsCi(pObj) || Aig_ObjIsConst1(pObj) ) continue;
            a = pVals[Aig_ObjFaninId0(pObj)] ^ Aig_ObjFaninC0(pObj);
            if ( Aig_ObjIsCo(pObj) || Aig_ObjIsBuf(pObj) ) pVals[i] = a;
            else
            {
                b = pVals[Aig_ObjFaninId1(pObj)] ^ Aig_ObjFaninC1(pObj);
                pVals[i] = Aig_ObjIsExor(pObj) ? a ^ b : a & b;
            }
        }
        Aig_ManForEachCo( pAig, pObj, i )
            Vec_IntPush( vAssump, Abc_Var2Lit(Gip_CtxObjVar(p, pObj), !pVals[Aig_ObjId(pObj)]) );
        Ret = Gip_SolverSolve( pSat, Vec_IntArray(vAssump), Vec_IntSize(vAssump), NULL, NULL, 0, -1 );
        if ( Ret != GIP_SAT ) Abc_Print( 1, "CNF TRUTH CHECK FAILED: assignment %d should be SAT.\n", Mask );
        assert( Ret == GIP_SAT );
        for ( j = nAssumedCis; j < Vec_IntSize(vAssump); j++ )
        {
            Lit = Vec_IntEntry( vAssump, j );
            Vec_IntWriteEntry( vAssump, j, Lit ^ 1 );
            Ret = Gip_SolverSolve( pSat, Vec_IntArray(vAssump), Vec_IntSize(vAssump), NULL, NULL, 0, -1 );
            if ( Ret != GIP_UNSAT ) Abc_Print( 1, "CNF TRUTH CHECK FAILED: assignment %d output %d.\n", Mask, j - nAssumedCis );
            assert( Ret == GIP_UNSAT );
            Vec_IntWriteEntry( vAssump, j, Lit );
        }
    }
    ABC_FREE( pVals );
    Vec_IntFree( vAssump );
    Gip_SolverFree( pSat );
}

/**Function*************************************************************

  Synopsis    [Creates the shared GipSAT context.]

  Description [Derives a full static CNF over the entire AIG and builds
  the CSR dependency table dep(v) = variables appearing in the defining
  clauses of v. Shared read-only by all frame solvers.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
typedef struct Gip_Bve_t_ Gip_Bve_t;
struct Gip_Bve_t_
{
    Vec_Ptr_t * vClauses;
    Vec_Int_t * vOwners;
    Vec_Wec_t * vDefs;
    Vec_Wec_t * vUses;
};

/**Function*************************************************************

  Synopsis    [Records a clause and its variable occurrences for elimination.]

  Description []

***********************************************************************/
static void Gip_BveAdd( Gip_Bve_t * p, int Owner, Vec_Int_t * vClause )
{
    int Id = Vec_PtrSize(p->vClauses), i, Lit;
    Vec_PtrPush(p->vClauses,vClause); Vec_IntPush(p->vOwners,Owner);
    Vec_WecPush(p->vDefs,Owner,Id);
    Vec_IntForEachEntry(vClause,Lit,i)
        if ( Gip_LitVar(Lit) != Owner ) Vec_WecPush(p->vUses,Gip_LitVar(Lit),Id);
}

/**Function*************************************************************

  Synopsis    [Removes deleted clause references from an occurrence list.]

  Description []

***********************************************************************/
static void Gip_BveCompact( Gip_Bve_t * p, Vec_Int_t * vIds )
{
    int i, Id, n = 0;
    Vec_IntForEachEntry(vIds,Id,i)
        if ( Vec_PtrEntry(p->vClauses,Id) ) Vec_IntWriteEntry(vIds,n++,Id);
    Vec_IntShrink(vIds,n);
}

/**Function*************************************************************

  Synopsis    [Removes a clause from the elimination database.]

  Description []

***********************************************************************/
static void Gip_BveDelete( Gip_Bve_t * p, Vec_Int_t * vIds )
{
    int i, Id;
    Vec_IntForEachEntry(vIds,Id,i)
    {
        Vec_Int_t * vClause = (Vec_Int_t *)Vec_PtrEntry(p->vClauses,Id);
        if ( vClause ) Vec_IntFree(vClause);
        Vec_PtrWriteEntry(p->vClauses,Id,NULL);
    }
    Vec_IntClear(vIds);
}

/**Function*************************************************************

  Synopsis    [Resolves two clauses on a pivot subject to a clause-size limit.]

  Description []

***********************************************************************/
// Both inputs are sorted and contain opposite pivot literals. NULL denotes
// a tautological resolvent. An oversized clause rejects the whole candidate.
static Vec_Int_t * Gip_BveResolve( Vec_Int_t * a, Vec_Int_t * b, int Var, int * pTooLong )
{
    Vec_Int_t * r = Vec_IntAlloc(Vec_IntSize(a)+Vec_IntSize(b));
    int i = 0, j = 0, Lit;
    while ( i < Vec_IntSize(a) || j < Vec_IntSize(b) )
    {
        if ( j == Vec_IntSize(b) || (i < Vec_IntSize(a) && Vec_IntEntry(a,i) < Vec_IntEntry(b,j)) )
            Lit = Vec_IntEntry(a,i++);
        else Lit = Vec_IntEntry(b,j++);
        if ( Gip_LitVar(Lit) == Var ) continue;
        if ( Vec_IntSize(r) && Vec_IntEntryLast(r) == (Lit^1) ) { Vec_IntFree(r); return NULL; }
        if ( !Vec_IntSize(r) || Vec_IntEntryLast(r) != Lit ) Vec_IntPush(r,Lit);
        if ( Vec_IntSize(r) > 64 ) { *pTooLong = 1; Vec_IntFree(r); return NULL; }
    }
    assert(Vec_IntSize(r));
    return r;
}

/**Function*************************************************************

  Synopsis    [Eliminates internal variables using their defining clauses and bounded resolution.]

  Description []

***********************************************************************/
// Substitute a total functional definition into its consumers. Resolving
// definition clauses against uses is sufficient: the definition supplies
// a unique value for the eliminated variable for every remaining CI value.
// Keep the consumer as each new clause's owner, so dependencies stay a DAG.
// CIs, COs, and the constant are frozen, preserving every query interface.
static Cnf_Dat_t * Gip_CnfBve( Aig_Man_t * pAig, Cnf_Dat_t * pOld )
{
    int Seconds = Gip_OptionGet("PDR2_BVE") ? Abc_MaxInt(0,Abc_MinInt(60,atoi(Gip_OptionGet("PDR2_BVE")))) : 0;
    int Tight = Gip_OptionGet("PDR2_BVE_LITS") && atoi(Gip_OptionGet("PDR2_BVE_LITS"));
    int nObjs = Aig_ManObjNumMax(pAig), i, c, j, k, Var, Id, Lit, nElim = 0;
    int nClauses = 0, nLiterals = 0, * pOwners, * pData;
    abctime Start = Abc_Clock(), Stop = Start+(abctime)Seconds*CLOCKS_PER_SEC;
    Gip_Bve_t B = {0};
    Cnf_Dat_t * pNew;
    Aig_Obj_t * pObj;
    Vec_Int_t * vClause, * vUses, * vDefs, * vNewOwners;
    Vec_Ptr_t * vNew;
    if ( !Seconds || nObjs > 1000000 || pOld->nClauses <= 0 || pOld->nClauses > 10000000 ) return pOld;
    pOwners = ABC_ALLOC(int,pOld->nClauses);
    for ( c = 0; c < pOld->nClauses; c++ ) pOwners[c] = -1;
    for ( i = 0; i < nObjs; i++ )
        for ( c = pOld->pObj2Clause[i]; c < pOld->pObj2Clause[i]+pOld->pObj2Count[i]; c++ )
        {
            assert(c >= 0 && c < pOld->nClauses && pOwners[c] == -1);
            pOwners[c] = i;
        }
    for ( c = 0; c < pOld->nClauses; c++ ) if ( pOwners[c] < 0 ) { ABC_FREE(pOwners); return pOld; }
    B.vClauses = Vec_PtrAlloc(pOld->nClauses); B.vOwners = Vec_IntAlloc(pOld->nClauses);
    B.vDefs = Vec_WecStart(nObjs); B.vUses = Vec_WecStart(nObjs);
    for ( c = 0; c < pOld->nClauses; c++ )
    {
        vClause = Vec_IntAlloc(pOld->pClauses[c+1]-pOld->pClauses[c]);
        Vec_IntPushArray(vClause,pOld->pClauses[c],pOld->pClauses[c+1]-pOld->pClauses[c]);
        Vec_IntSort(vClause,0);
        Gip_BveAdd(&B,pOwners[c],vClause);
    }
    ABC_FREE(pOwners);
    vNew = Vec_PtrAlloc(100); vNewOwners = Vec_IntAlloc(100);
    Aig_ManForEachNode(pAig,pObj,Var)
    {
        int nOldCost, nOldLits = 0, nNewLits = 0, Failed = 0;
        if ( Abc_Clock() >= Stop || Vec_PtrSize(B.vClauses) > 4*pOld->nClauses ) break;
        vDefs = Vec_WecEntry(B.vDefs,Var); vUses = Vec_WecEntry(B.vUses,Var);
        Gip_BveCompact(&B,vDefs); Gip_BveCompact(&B,vUses);
        nOldCost = Vec_IntSize(vDefs)+Vec_IntSize(vUses);
        if ( !Vec_IntSize(vDefs) || nOldCost > 128 ) continue;
        Vec_IntForEachEntry(vDefs,Id,i)
        {
            vClause = (Vec_Int_t *)Vec_PtrEntry(B.vClauses,Id);
            nOldLits += Vec_IntSize(vClause);
            if ( Vec_IntFind(vClause,Gip_Lit(Var,0)) < 0 && Vec_IntFind(vClause,Gip_Lit(Var,1)) < 0 ) Failed = 1;
        }
        Vec_IntForEachEntry(vUses,Id,i) nOldLits += Vec_IntSize((Vec_Int_t *)Vec_PtrEntry(B.vClauses,Id));
        Vec_IntForEachEntry(vUses,Id,i)
        {
            int DefId, Pivot;
            Vec_Int_t * vUse = (Vec_Int_t *)Vec_PtrEntry(B.vClauses,Id);
            if ( Failed ) break;
            Pivot = Vec_IntFind(vUse,Gip_Lit(Var,0)) >= 0 ? Gip_Lit(Var,0) : Gip_Lit(Var,1);
            assert(Vec_IntFind(vUse,Pivot) >= 0 && Vec_IntEntry(B.vOwners,Id) > Var);
            Vec_IntForEachEntry(vDefs,DefId,j)
            {
                Vec_Int_t * vDef = (Vec_Int_t *)Vec_PtrEntry(B.vClauses,DefId);
                if ( Vec_IntFind(vDef,Pivot^1) < 0 ) continue;
                vClause = Gip_BveResolve(vUse,vDef,Var,&Failed);
                if ( vClause )
                {
                    Vec_PtrPush(vNew,vClause); Vec_IntPush(vNewOwners,Vec_IntEntry(B.vOwners,Id));
                    nNewLits += Vec_IntSize(vClause);
                }
                if ( Vec_PtrSize(vNew) > nOldCost || nNewLits > (Tight ? 1 : 2)*nOldLits ) Failed = 1;
                if ( Failed ) break;
            }
        }
        if ( !Failed )
        {
            Gip_BveDelete(&B,vDefs); Gip_BveDelete(&B,vUses); nElim++;
            Vec_PtrForEachEntry(Vec_Int_t *,vNew,vClause,i) Gip_BveAdd(&B,Vec_IntEntry(vNewOwners,i),vClause);
        }
        else Vec_PtrForEachEntry(Vec_Int_t *,vNew,vClause,i) Vec_IntFree(vClause);
        Vec_PtrClear(vNew); Vec_IntClear(vNewOwners);
    }
    Vec_PtrForEachEntry(Vec_Int_t *,B.vClauses,vClause,i) if ( vClause ) nClauses++, nLiterals += Vec_IntSize(vClause);
    pNew = ABC_CALLOC(Cnf_Dat_t,1);
    pNew->pMan = pAig; pNew->nVars = pOld->nVars; pNew->nClauses = nClauses; pNew->nLiterals = nLiterals;
    pNew->pObj2Clause = ABC_ALLOC(int,nObjs); pNew->pObj2Count = ABC_CALLOC(int,nObjs);
    pNew->pClauses = ABC_ALLOC(int *,nClauses+1);
    pData = ABC_ALLOC(int,Abc_MaxInt(1,nLiterals)); c = k = 0;
    for ( Var = 0; Var < nObjs; Var++ )
    {
        pNew->pObj2Clause[Var] = c;
        Vec_IntForEachEntry(Vec_WecEntry(B.vDefs,Var),Id,i)
        {
            vClause = (Vec_Int_t *)Vec_PtrEntry(B.vClauses,Id);
            if ( !vClause ) continue;
            pNew->pClauses[c++] = pData+k; pNew->pObj2Count[Var]++;
            Vec_IntForEachEntry(vClause,Lit,j) pData[k++] = Lit;
        }
    }
    pNew->pClauses[c] = pData+k;
    assert(c == nClauses && k == nLiterals);
    Abc_Print(1,"CNF elimination: %d internal variables, clauses %d -> %d, literals %d -> %d. Time = %.3f sec.\n",
        nElim,pOld->nClauses,nClauses,pOld->nLiterals,nLiterals,(double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
    Vec_PtrForEachEntry(Vec_Int_t *,B.vClauses,vClause,i) if ( vClause ) Vec_IntFree(vClause);
    Vec_PtrFree(B.vClauses); Vec_IntFree(B.vOwners); Vec_WecFree(B.vDefs); Vec_WecFree(B.vUses);
    Vec_PtrFree(vNew); Vec_IntFree(vNewOwners); Cnf_DataFree(pOld);
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Encodes the circuit and builds the solver variable dependency table.]

  Description []

***********************************************************************/
static Gip_Ctx_t * Gip_CtxCreateInt( Aig_Man_t * pAig, Cnf_Man_t * pCnfMan, int fCompact, int fPdr2 )
{
    Gip_Ctx_t * p;
    int * pStamp;   // per-var stamp for dedup while collecting deps
    int * pCount;   // per-var dep count (pass 1)
    int ObjId, i, c, w, u, nObjs;
    int * pLit, * pStop;
    p = ABC_CALLOC( Gip_Ctx_t, 1 );
    p->pAig  = pAig;
    p->iUnusedPiVar = -1;
    p->fPdr2 = fPdr2;
    if ( fPdr2 )
    {
        int Mode = Gip_OptionGet("PDR2_CNF") ? atoi(Gip_OptionGet("PDR2_CNF")) : 0;
        p->pCnf = Mode == 1 || Mode == 2 ? Gip_CnfStructural(pAig, Mode) : Cnf_DeriveOtherWithMan(pCnfMan, pAig, 0);
        p->pCnf = Gip_CnfBve(pAig,p->pCnf);
        if ( Gip_OptionGet("PDR2_CNF_STATS") )
            Abc_Print( 1, "CNF encoding %d: %d clauses, %d literals.\n", Mode, p->pCnf->nClauses, p->pCnf->nLiterals );
    }
    else
        p->pCnf = Cnf_DeriveOtherWithMan( pCnfMan, pAig, 0 );
    p->nVars = p->pCnf->nVars;
    assert( p->nVars == Aig_ManObjNumMax(pAig) );
    nObjs = Aig_ManObjNumMax( pAig );
    if ( fCompact )
    {
        Aig_Obj_t * pObj;
        int fUnusedPi = Gip_OptionGet("PDR2_UNUSED_PI") && atoi(Gip_OptionGet("PDR2_UNUSED_PI"));
        int nPis = Aig_ManCiNum(pAig) - Aig_ManRegNum(pAig), nUnused = 0;
        // CNF mapping absorbs many internal AIG nodes. Avoid allocating SAT
        // state for those unused IDs in every frame. Preserve relative variable
        // order, including unused CIs that the model/lifting interface accesses.
        p->pObj2Var = ABC_ALLOC( int, nObjs );
        for ( i = 0; i < nObjs; i++ )
            p->pObj2Var[i] = -1;
        Aig_ManForEachCi( pAig, pObj, i )
            if ( !fUnusedPi || i >= nPis || Aig_ObjRefs(pObj) > 0 )
                p->pObj2Var[Aig_ObjId(pObj)] = 0;
        for ( pLit = p->pCnf->pClauses[0]; pLit < p->pCnf->pClauses[p->pCnf->nClauses]; pLit++ )
            p->pObj2Var[Gip_LitVar(*pLit)] = 0;
        p->nVars = 0;
        for ( i = 0; i < nObjs; i++ )
            if ( p->pObj2Var[i] == 0 )
                p->pObj2Var[i] = p->nVars++;
        // Unreferenced PIs never occur in a clause or a transition function.
        // Map them to one unused variable so the model/lifting interface can
        // still read every original PI, without changing the AIG or its order.
        // Registers always retain distinct variables, even when unreferenced.
        if ( fUnusedPi )
        {
            int Alias = p->nVars;
            Aig_ManForEachCi( pAig, pObj, i )
                if ( p->pObj2Var[Aig_ObjId(pObj)] < 0 )
                {
                    assert( i < nPis && Aig_ObjRefs(pObj) == 0 );
                    p->pObj2Var[Aig_ObjId(pObj)] = Alias;
                    nUnused++;
                }
            if ( nUnused ) p->iUnusedPiVar = p->nVars++;
        }
        p->pVar2Obj = ABC_ALLOC( int, p->nVars );
        for ( i = 0; i < nObjs; i++ )
            if ( p->pObj2Var[i] >= 0 )
                p->pVar2Obj[p->pObj2Var[i]] = i;
        for ( pLit = p->pCnf->pClauses[0]; pLit < p->pCnf->pClauses[p->pCnf->nClauses]; pLit++ )
        {
            *pLit = Gip_Lit( p->pObj2Var[Gip_LitVar(*pLit)], Gip_LitCompl(*pLit) );
            assert( Gip_LitVar(*pLit) != p->iUnusedPiVar );
        }
        p->pCnf->nVars = p->nVars;
        if ( fUnusedPi )
            Abc_Print(1, "Unused PI compaction: %d inputs share one unused SAT variable; %d SAT variables remain.\n", nUnused, p->nVars);
    }
    p->varConst = Gip_CtxObjVar( p, Aig_ManConst1(pAig) );
    assert( p->varConst >= 0 && p->varConst < p->nVars );

    // pass 1: count deps per defined var
    pCount = ABC_CALLOC( int, p->nVars );
    pStamp = ABC_ALLOC( int, p->nVars );
    for ( i = 0; i < p->nVars; i++ )
        pStamp[i] = -1;
    for ( ObjId = 0; ObjId < nObjs; ObjId++ )
    {
        if ( p->pCnf->pObj2Count[ObjId] <= 0 )
            continue;
        w = p->pObj2Var ? p->pObj2Var[ObjId] : ObjId;
        assert( w >= 0 );
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
        w = p->pObj2Var ? p->pObj2Var[ObjId] : ObjId;
        assert( w >= 0 );
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
    if ( fPdr2 && Gip_OptionGet("PDR2_CNF_CHECK") ) Gip_CtxCheckTruth( p );
    return p;
}

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
    return Gip_CtxCreateInt( pAig, pCnfMan, 0, 0 );
}

/**Function*************************************************************

  Synopsis    [Creates a pdr2 context with optional variable compaction.]

  Description []

***********************************************************************/
Gip_Ctx_t * Gip_CtxCreatePdr2( Aig_Man_t * pAig, Cnf_Man_t * pCnfMan, int fCompact )
{
    return Gip_CtxCreateInt( pAig, pCnfMan, fCompact, 1 );
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
    ABC_FREE( p->pObj2Var );
    ABC_FREE( p->pVar2Obj );
    ABC_FREE( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
