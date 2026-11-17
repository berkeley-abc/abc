/**CFile****************************************************************

  FileName    [acec2Truth.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Arithmetic analysis and equivalence checking.]

  Synopsis    [Exact matching of small arithmetic cones over shared cuts.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 13, 2026.]

  Revision    [$Id$]

***********************************************************************/

#include "acec2Int.h"
#include "misc/util/utilTruth.h"
#include "misc/vec/vecHsh.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

enum { ACEC2_TRUTH_VARS = 14, ACEC2_TRUTH_WORDS = 1 << (ACEC2_TRUTH_VARS-6) };

struct Acec2_TruthCache_t_
{
    Vec_Int_t * vCuts, * vIndex, * vStops;
    Vec_Wrd_t * vTruths;
};

typedef struct Acec2_Truth_t_ Acec2_Truth_t;
struct Acec2_Truth_t_
{
    Acec2_Par_t * pPars;
    abctime Deadline;
    Hsh_VecMan_t * pHash;
    Vec_Int_t * vColors, * vFrontier;
    Vec_Int_t * vReprs, * vSides, * vFixed, * vKey;
    Vec_Wec_t * vMembers;
    ABC_INT64_T nSteps, nStepLimit;
    int nComputed, nLimited, nReused;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Merges ordered supports without exceeding the truth limit.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_TruthMerge( int * pA, int nA, int * pB, int nB, int * pOut )
{
    int i = 0, j = 0, k = 0, x;
    while ( i < nA || j < nB )
    {
        if ( i < nA && (j == nB || pA[i] < pB[j]) ) x = pA[i++];
        else if ( j < nB && (i == nA || pB[j] < pA[i]) ) x = pB[j++];
        else { x = pA[i++]; j++; }
        if ( k == ACEC2_TRUTH_VARS ) return -1;
        pOut[k++] = x;
    }
    return k;
}

/**Function*************************************************************

  Synopsis    [Stores a complete cut truth table in private packed vectors.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_TruthStore( Vec_Int_t * vCuts, Vec_Wrd_t * vTruths, int * pSupp, int nVars, word * pTruth )
{
    int Offset = Vec_IntSize(vCuts), i;
    Vec_IntPushTwo(vCuts, nVars, Vec_WrdSize(vTruths));
    for ( i = 0; i < nVars; i++ ) Vec_IntPush(vCuts, pSupp[i]);
    for ( i = 0; i < Abc_TtWordNum(nVars); i++ ) Vec_WrdPush(vTruths, pTruth[i]);
    return Offset;
}

/**Function*************************************************************

  Synopsis    [Releases cached exact functions belonging to one source design.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Acec2_TruthCacheStop( Acec2_TruthCache_t * p )
{
    if ( !p ) return;
    Vec_IntFree(p->vCuts); Vec_IntFree(p->vIndex); Vec_IntFree(p->vStops);
    Vec_WrdFree(p->vTruths); ABC_FREE(p);
}

/**Function*************************************************************

  Synopsis    [Invalidates only functions whose independent frontier changed.]

  Description [A bound node is keyed by its exact destination literal,
  including phase. An unbound gate remains valid only if both fanin functions
  remain valid. Source graphs are immutable. This complete linear pass is
  atomic with respect to cache validity; cancellation is checked around it.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Acec2_TruthCache_t * Acec2_TruthCacheUpdate( Acec2_Man_t * m, Vec_Int_t * vMap, Vec_Int_t * vFrontier )
{
    Acec2_TruthCache_t * p = m->pTruthCache;
    Gia_Man_t * g = m->pGia; Gia_Obj_t * o; Vec_Bit_t * valid;
    int i, lit, stop, good; word zero = 0;
    if ( p && (Vec_IntSize(p->vCuts) > 3000000 || Vec_WrdSize(p->vTruths) > 2000000) )
    { Acec2_TruthCacheStop(p); m->pTruthCache = p = NULL; }
    if ( !p )
    {
        m->pTruthCache = p = ABC_CALLOC(Acec2_TruthCache_t, 1);
        p->vCuts = Vec_IntAlloc(1000); p->vTruths = Vec_WrdAlloc(1000);
        p->vIndex = Vec_IntStartFull(Gia_ManObjNum(g)); p->vStops = Vec_IntStartFull(Gia_ManObjNum(g));
        Acec2_TruthStore(p->vCuts, p->vTruths, NULL, 0, &zero); Vec_IntWriteEntry(p->vIndex, 0, 0);
    }
    valid = Vec_BitStart(Gia_ManObjNum(g)); Acec2_BitWrite(valid, 0, 1);
    Gia_ManForEachObj1(g, o, i)
    {
        if ( Gia_ObjIsCo(o) ) continue;
        lit = Vec_IntEntry(vMap, i); stop = Vec_IntEntry(vFrontier, lit >> 1) ? lit : -1;
        good = Vec_IntEntry(p->vIndex, i) >= 0 && stop == Vec_IntEntry(p->vStops, i);
        if ( good && stop < 0 ) good = Gia_ObjIsAnd(o) &&
            Vec_BitEntry(valid, Gia_ObjFaninId0(o, i)) && Vec_BitEntry(valid, Gia_ObjFaninId1(o, i));
        if ( !good ) Vec_IntWriteEntry(p->vIndex, i, -1);
        Acec2_BitWrite(valid, i, good); Vec_IntWriteEntry(p->vStops, i, stop);
    }
    Vec_BitFree(valid); return p;
}

/**Function*************************************************************

  Synopsis    [Groups equal functions using complete support and truth keys.]

  Description [Phase normalization permits complemented matches. A hash
  collision alone never authorizes a replacement. Existing common interfaces
  take precedence over other representatives, whose node IDs only break ties.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_TruthClass( Acec2_Truth_t * p, int Side, int Id, int Lit, int Replace,
                             int * pSupp, int nVars, word * pTruth )
{
    int i, Phase = (int)(pTruth[0] & 1), Old = Hsh_VecSize(p->pHash), Class;
    int Fixed = Vec_IntEntry(p->vColors, Lit >> 1) == 3;
    int Canonical = (Fixed || Replace < 0 ? Lit : Replace) ^ Phase;
    word t;
    Vec_IntClear(p->vKey); Vec_IntPush(p->vKey, nVars);
    for ( i = 0; i < nVars; i++ ) Vec_IntPush(p->vKey, pSupp[i]);
    for ( i = 0; i < Abc_TtWordNum(nVars); i++ )
    {
        t = Phase ? ~pTruth[i] : pTruth[i];
        Vec_IntPushTwo(p->vKey, (int)(unsigned)t, (int)(unsigned)(t >> 32));
    }
    Class = Hsh_VecManAdd(p->pHash, p->vKey);
    if ( Class == Old )
    {
        Vec_IntPush(p->vReprs, Canonical); Vec_IntPush(p->vSides, 1 << Side);
        Vec_IntPush(p->vFixed, Fixed); Vec_WecPushLevel(p->vMembers);
    }
    else
    {
        Vec_IntWriteEntry(p->vSides, Class, Vec_IntEntry(p->vSides, Class) | (1 << Side));
        if ( Fixed && !Vec_IntEntry(p->vFixed, Class) ) Vec_IntWriteEntry(p->vReprs, Class, Canonical);
        else if ( Fixed || !Vec_IntEntry(p->vFixed, Class) )
            Vec_IntWriteEntry(p->vReprs, Class, Abc_MinInt(Vec_IntEntry(p->vReprs, Class), Canonical));
        if ( Fixed ) Vec_IntWriteEntry(p->vFixed, Class, 1);
    }
    Vec_IntPushTwo(Vec_WecEntry(p->vMembers, Class), Side, Abc_Var2Lit(Id, Phase));
}

/**Function*************************************************************

  Synopsis    [Computes exact functions of one design over the shared cut.]

  Description [Selected cell and parity nodes are candidates. Their cones
  stop at proved shared operand signals, treated as independent variables.
  Each side gets its own deterministic work and storage allowance. Exceeding
  a support or resource bound leaves that function unknown.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Acec2_TruthSide( Acec2_Truth_t * p, Acec2_Man_t * m, Vec_Int_t * vMap, Vec_Int_t * vReplace, int Side )
{
    Gia_Man_t * g = m->pGia;
    Gia_Obj_t * o;
    Acec2_TruthCache_t * cache;
    Vec_Int_t * vCuts, * vIndex;
    Vec_Wrd_t * vTruths;
    Vec_Bit_t * vNeeded;
    int i, j, Lit, a, b, Offset, OffsetA, OffsetB, nA, nB, nVars, nWords;
    int Supp[ACEC2_TRUTH_VARS], * pA, * pB, KeyStart, nMembers = 0;
    word TruthA[ACEC2_TRUTH_WORDS], TruthB[ACEC2_TRUTH_WORDS];
    ABC_INT64_T Steps = 0, Cost;
    if ( Gia_ManXorNum(g) || Gia_ManMuxNum(g) || Acec2_Stop(p->pPars, p->Deadline) ) return;
    cache = Acec2_TruthCacheUpdate(m, vMap, p->vFrontier);
    vCuts = cache->vCuts; vTruths = cache->vTruths; vIndex = cache->vIndex;
    vNeeded = Vec_BitStart(Gia_ManObjNum(g));
    KeyStart = Vec_IntSize(p->pHash->vData);
    Gia_ManForEachAnd(g, o, i)
    {
        if ( (i & 255) == 0 && Acec2_Stop(p->pPars, p->Deadline) ) goto finish;
        if ( Vec_IntEntry(p->vColors, Vec_IntEntry(vMap, i) >> 1) != 3 &&
             (Vec_IntEntry(m->vOwner, i) >= 0 || Vec_IntEntry(m->vXorFirst, i) >= 0) )
            Acec2_BitWrite(vNeeded, i, 1);
    }
    for ( i = Gia_ManObjNum(g)-1; i > 0; i-- )
    {
        if ( (i & 255) == 0 && Acec2_Stop(p->pPars, p->Deadline) ) goto finish;
        if ( !Vec_BitEntry(vNeeded, i) || Vec_IntEntry(p->vFrontier, Vec_IntEntry(vMap, i) >> 1) ) continue;
        o = Gia_ManObj(g, i);
        if ( !Gia_ObjIsAnd(o) ) continue;
        Acec2_BitWrite(vNeeded, Gia_ObjFaninId0(o, i), 1);
        Acec2_BitWrite(vNeeded, Gia_ObjFaninId1(o, i), 1);
    }
    Gia_ManForEachObj1(g, o, i)
    {
        if ( (i & 255) == 0 && Acec2_Stop(p->pPars, p->Deadline) ) goto finish;
        if ( !Vec_BitEntry(vNeeded, i) || Gia_ObjIsCo(o) ) continue;
        Lit = Vec_IntEntry(vMap, i);
        Offset = Vec_IntEntry(vIndex, i);
        if ( Offset >= 0 )
        {
            nVars = Vec_IntEntry(vCuts, Offset);
            for ( j = 0; j < nVars; j++ ) Supp[j] = Vec_IntEntry(vCuts, Offset+2+j);
            memcpy(TruthA, Vec_WrdEntryP(vTruths, Vec_IntEntry(vCuts, Offset+1)), sizeof(word)*Abc_TtWordNum(nVars));
            p->nReused++;
        }
        else if ( Vec_IntEntry(p->vFrontier, Lit >> 1) )
        {
            nVars = Lit < 2 ? 0 : 1; Supp[0] = Lit >> 1;
            TruthA[0] = Lit < 2 ? (Lit ? ~(word)0 : 0) :
                (Lit & 1) ? ABC_CONST(0x5555555555555555) : ABC_CONST(0xAAAAAAAAAAAAAAAA);
        }
        else
        {
            if ( !Gia_ObjIsAnd(o) ) continue;
            a = Gia_ObjFaninId0(o, i); b = Gia_ObjFaninId1(o, i);
            OffsetA = Vec_IntEntry(vIndex, a); OffsetB = Vec_IntEntry(vIndex, b);
            if ( OffsetA < 0 || OffsetB < 0 ) continue;
            nA = Vec_IntEntry(vCuts, OffsetA); nB = Vec_IntEntry(vCuts, OffsetB);
            // A zero-support cut can end exactly at the end of the vector.
            pA = Vec_IntArray(vCuts)+OffsetA+2; pB = Vec_IntArray(vCuts)+OffsetB+2;
            nVars = Acec2_TruthMerge(pA, nA, pB, nB, Supp);
            if ( nVars < 0 ) continue;
            nWords = Abc_TtWordNum(nVars); Cost = (ABC_INT64_T)(nVars+2)*nWords;
            if ( Steps+Cost > p->nStepLimit ) { p->nLimited++; break; }
            Steps += Cost;
            memcpy(TruthA, Vec_WrdEntryP(vTruths, Vec_IntEntry(vCuts, OffsetA+1)), sizeof(word)*Abc_TtWordNum(nA));
            memcpy(TruthB, Vec_WrdEntryP(vTruths, Vec_IntEntry(vCuts, OffsetB+1)), sizeof(word)*Abc_TtWordNum(nB));
            Abc_TtStretch6(TruthA, nA, nVars); Abc_TtStretch6(TruthB, nB, nVars);
            Abc_TtExpand(TruthA, nVars, pA, nA, Supp, nVars); Abc_TtExpand(TruthB, nVars, pB, nB, Supp, nVars);
            for ( j = 0; j < nWords; j++ )
                TruthA[j] = (Gia_ObjFaninC0(o) ? ~TruthA[j] : TruthA[j]) & (Gia_ObjFaninC1(o) ? ~TruthB[j] : TruthB[j]);
            nVars = Abc_TtMinBase(TruthA, Supp, nVars, nVars); p->nComputed++;
        }
        if ( (Offset < 0 && (Vec_IntSize(vCuts)+nVars+2 > 6000000 || Vec_WrdSize(vTruths)+Abc_TtWordNum(nVars) > 4000000)) ||
             Vec_IntSize(p->pHash->vData)-KeyStart > 8000000 || Hsh_VecSize(p->pHash) >= 100000 || nMembers >= 1000000 )
        { p->nLimited++; break; }
        if ( Offset < 0 )
        { Offset = Acec2_TruthStore(vCuts, vTruths, Supp, nVars, TruthA); Vec_IntWriteEntry(vIndex, i, Offset); }
        if ( !Vec_IntEntry(p->vFrontier, Lit >> 1) && Vec_IntEntry(m->vOwner, i) < 0 && Vec_IntEntry(m->vXorFirst, i) < 0 ) continue;
        Acec2_TruthClass(p, Side, i, Lit, Vec_IntEntry(vReplace, i), Supp, nVars, TruthA); nMembers++;
    }
finish:
    p->nSteps += Steps;
    Vec_BitFree(vNeeded);
}

/**Function*************************************************************

  Synopsis    [Pins both sides of completed cross-design function classes.]

  Description [The representative is pinned even if its literal does not
  change. Otherwise rebuilding it can lose the just-proved correspondence.
  Existing shared interfaces are left in place.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Acec2_TruthCommit( Acec2_Truth_t * p, Vec_Int_t ** vMaps, Vec_Int_t ** vReplaces )
{
    Vec_Int_t * v;
    int Class, j, Side, Lit, Id, Canonical, Old, nChanged = 0;
    Vec_WecForEachLevel(p->vMembers, v, Class)
    {
        if ( (Class & 255) == 0 && Acec2_Stop(p->pPars, p->Deadline) ) break;
        if ( Vec_IntEntry(p->vSides, Class) != 3 ) continue;
        for ( j = 0; j < Vec_IntSize(v); j += 2 )
        {
            Side = Vec_IntEntry(v, j); Lit = Vec_IntEntry(v, j+1); Id = Lit >> 1;
            if ( !Id || Vec_IntEntry(p->vColors, Vec_IntEntry(vMaps[Side], Id) >> 1) == 3 ) continue;
            Canonical = Vec_IntEntry(p->vReprs, Class) ^ (Lit & 1);
            Old = Vec_IntEntry(vReplaces[Side], Id);
            if ( Old < 0 ) Old = Vec_IntEntry(vMaps[Side], Id);
            Vec_IntWriteEntry(vReplaces[Side], Id, Canonical); nChanged += Old != Canonical;
        }
    }
    return nChanged;
}

/**Function*************************************************************

  Synopsis    [Matches bounded arithmetic functions independently of encoding.]

  Description [Frontier literals already denote proved common functions.
  Equal complete truth tables over the same independent variables establish
  exact aliases, including complemented aliases. No simulation agreement or
  partial truth table is accepted as a proof. Other cones remain for arithmetic
  component proofs and ordinary CEC. The source graphs are never modified.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Acec2_MatchTruth( Gia_Man_t * pNew, Acec2_Man_t ** pMans, Vec_Int_t ** vMaps, Vec_Int_t ** vReplaces,
                     Vec_Int_t * vFrontier, Acec2_Par_t * pPars, abctime Deadline )
{
    Acec2_Truth_t Data, * p = &Data;
    Acec2_Par_t Pars = *pPars;
    int Side, i, Lit, nChanged = 0, Cancelled = 0;
    if ( !Pars.pCancelled ) Pars.pCancelled = &Cancelled;
    pPars = &Pars;
    if ( !pMans[0] || !pMans[1] || Acec2_Stop(pPars, Deadline) ) return 0;
    memset(p, 0, sizeof(Acec2_Truth_t));
    p->pPars = pPars; p->Deadline = Deadline; p->vFrontier = vFrontier; p->nStepLimit = 32000000;
    p->vColors = Vec_IntStart(Gia_ManObjNum(pNew)); p->pHash = Hsh_VecManStart(1000);
    p->vReprs = Vec_IntAlloc(1000); p->vSides = Vec_IntAlloc(1000); p->vFixed = Vec_IntAlloc(1000);
    p->vMembers = Vec_WecAlloc(1000); p->vKey = Vec_IntAlloc(1000);
    for ( Side = 0; Side < 2; Side++ )
        Vec_IntForEachEntry(vMaps[Side], Lit, i)
        {
            if ( (i & 255) == 0 && Acec2_Stop(pPars, Deadline) ) goto finish;
            Vec_IntWriteEntry(p->vColors, Lit >> 1, Vec_IntEntry(p->vColors, Lit >> 1) | (1 << Side));
        }
    for ( Side = 0; Side < 2; Side++ ) Acec2_TruthSide(p, pMans[Side], vMaps[Side], vReplaces[Side], Side);
    if ( !Acec2_Stop(pPars, Deadline) ) nChanged = Acec2_TruthCommit(p, vMaps, vReplaces);
finish:
    if ( pPars->fVerbose )
        Abc_Print(1, "Exact cut matching: evaluated = %d, reused = %d, work = %lld, classes = %d, aliases = %d, limited sides = %d.\n",
            p->nComputed, p->nReused, (long long)p->nSteps, Hsh_VecSize(p->pHash), nChanged, p->nLimited);
    Vec_IntFree(p->vColors); Vec_IntFree(p->vReprs); Vec_IntFree(p->vSides); Vec_IntFree(p->vFixed);
    Vec_IntFree(p->vKey); Vec_WecFree(p->vMembers); Hsh_VecManStop(p->pHash);
    return nChanged;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
