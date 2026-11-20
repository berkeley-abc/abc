/**CFile****************************************************************

  FileName    [bmcBmcGia.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    [Incremental GIA bounded model checking with CaDiCaL.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 10, 2026.]

  Revision    [$Id: bmcBmcGia.c,v 1.00 2026/11/10 00:00:00 alanmi Exp $]

***********************************************************************/

#include <limits.h>
#include "bmc.h"
#include "misc/util/utilTruth.h"
#include "opt/drw/drw.h"
#include "sat/cnf/cnf.h"
#include "sat/cadical/ccadical.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Bmc3G_Man_t_ Bmc3G_Man_t;
typedef struct Bmc3G_Map_t_ Bmc3G_Map_t;
struct Bmc3G_Map_t_
{
    int *           pLits;
    unsigned char * pBits;
};
struct Bmc3G_Man_t_
{
    Bmc_GiaPar_t * pPars;
    Gia_Man_t *    pGia;
    Gia_Man_t *    pFrames;
    Gia_Man_t *    pOriginal;
    CCaDiCaL *     pSat;
    Vec_Ptr_t *   vMaps;
    Vec_Int_t *   vVars;
    Vec_Int_t *   vCopies;
    Vec_Int_t *   vCiMap;
    Vec_Int_t *   vRoots;
    Vec_Int_t *   vOriginalPos;
    Vec_Int_t *   vStack;
    Vec_Wrd_t *   vWork;
    Vec_Int_t *   vMapIds;
    abctime       Start;
    abctime       Deadline;
    abctime       PrepDeadline;
    int           nVars;
    int           fStopped;
    int           fFreeInit;
    int           nWindowQueries;
    int           nMapEntries;
    unsigned      nStopCalls;
    word          nMapBytes;
    word          nCnfLits;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Sets the incremental BMC defaults.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bmc_GiaSetDefaultParams( Bmc_GiaPar_t * pPars )
{
    memset( pPars, 0, sizeof(*pPars) );
    pPars->nLutSize = 6;
    pPars->nMemoryLimit = 8192;
    pPars->iFrame = -1;
}

/**Function*************************************************************

  Synopsis    [Checks a per-instance resource estimate before allocating more.]

  Description [Counts live original and learned clauses. Circuit literal
  charges remain conservative if simplification deletes defining clauses.
  A capacity allowance covers allocator and dynamically grown vector overhead.
  This is an allocation estimate, not process resident memory.]

  SideEffects [Latches a resource stop.]

  SeeAlso     [Bmc3G_Stop]

***********************************************************************/
static int Bmc3G_CheckMemory( Bmc3G_Man_t * p, double Extra )
{
    double Used = (double)(2 << 20) + Extra;
    if ( p->fStopped ) return 1;
    if ( p->pFrames && Gia_ManObjNum(p->pFrames) >= (1 << 28) ) goto limit;
    if ( p->pGia ) Used += 32.0 * p->pGia->nObjsAlloc;
    if ( p->pOriginal ) Used += 32.0 * p->pOriginal->nObjsAlloc;
    if ( p->pFrames ) Used += 64.0 * p->pFrames->nObjsAlloc;
    if ( p->vMaps ) Used += (double)p->nMapBytes + (double)Vec_PtrCap(p->vMaps) * sizeof(void *);
    if ( p->pSat )
    {
        ABC_INT64_T Clauses = ccadical_live_clauses( p->pSat );
        if ( Clauses < 0 ) goto limit;
        Used += 192.0 * p->nVars + 64.0 * Clauses + 8.0 * p->nCnfLits;
    }
    if ( 1.25 * (Used - Extra) / (1 << 20) > p->pPars->MemoryPeakMB )
        p->pPars->MemoryPeakMB = 1.25 * (Used - Extra) / (1 << 20);
    Used *= 1.25;
    if ( !p->pPars->nMemoryLimit ) return 0;
    if ( Used < (double)p->pPars->nMemoryLimit * (1 << 20) ) return 0;
limit:
    p->pPars->fMemoryLimit = p->fStopped = 1;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Latches cancellation in both construction and SAT search.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc3G_Stop( void * pData )
{
    Bmc3G_Man_t * p = (Bmc3G_Man_t *)pData;
    abctime Reserve = (abctime)(.0005 * p->pPars->MemoryPeakMB * CLOCKS_PER_SEC);
    if ( !p->fStopped )
        p->fStopped = (p->Deadline && Abc_Clock() >= p->Deadline - Reserve) ||
            (p->pPars->pFuncStop && p->pPars->pFuncStop(p->pPars->pStopData));
    if ( !p->fStopped && !(p->nStopCalls++ & 4095) ) Bmc3G_CheckMemory( p, 0 );
    return p->fStopped;
}

/**Function*************************************************************

  Synopsis    [Reads a saved literal or an unvisited entry.]

  Description [Constant-only maps use two bits per entry. Code three means
  unvisited, and codes zero and one are the corresponding constant literals.]

  SideEffects []

  SeeAlso     [Bmc3G_MapWrite]

***********************************************************************/
static inline int Bmc3G_MapRead( Bmc3G_Map_t * pMap, int Index )
{
    int Value;
    if ( pMap->pLits ) return pMap->pLits[Index];
    Value = (pMap->pBits[Index >> 2] >> (2 * (Index & 3))) & 3;
    assert( Value != 2 );
    return Value == 3 ? -1 : Value;
}

/**Function*************************************************************

  Synopsis    [Saves a literal, expanding a compact map when needed.]

  Description [A later demand may discover inputs in an earlier frame.
  Expansion retains every unvisited entry and every previously saved constant.]

  SideEffects [May allocate a dense map or latch the memory limit.]

  SeeAlso     [Bmc3G_MapRead]

***********************************************************************/
static int Bmc3G_MapWrite( Bmc3G_Man_t * p, Bmc3G_Map_t * pMap, int Index, int Lit )
{
    int i, * pLits;
    assert( Lit >= 0 && Index >= 0 && Index < p->nMapEntries );
    if ( !pMap->pLits && Lit > 1 )
    {
        if ( Bmc3G_CheckMemory(p, (double)p->nMapEntries * sizeof(int)) ) return 0;
        pLits = ABC_ALLOC( int, p->nMapEntries );
        for ( i = 0; i < p->nMapEntries; i++ )
        {
            if ( !(i & 1023) && Bmc3G_Stop(p) ) { ABC_FREE(pLits); return 0; }
            pLits[i] = Bmc3G_MapRead( pMap, i );
        }
        p->nMapBytes += (word)p->nMapEntries * sizeof(int) - (p->nMapEntries + 3) / 4;
        pMap->pLits = pLits;
        ABC_FREE( pMap->pBits );
    }
    if ( pMap->pLits )
        pMap->pLits[Index] = Lit;
    else
    {
        int Shift = 2 * (Index & 3);
        pMap->pBits[Index >> 2] = (unsigned char)
            ((pMap->pBits[Index >> 2] & ~(3 << Shift)) | (Lit << Shift));
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Allocates a constant or dense map for a new frame.]

  Description []

  SideEffects [Updates the manager's allocation estimate.]

  SeeAlso     [Bmc3G_MapWrite]

***********************************************************************/
static int Bmc3G_MapStart( Bmc3G_Man_t * p )
{
    size_t nBytes = p->pPars->nQueries ? (size_t)p->nMapEntries * sizeof(int) : (p->nMapEntries + 3) / 4;
    Bmc3G_Map_t * pMap;
    if ( Bmc3G_CheckMemory(p, sizeof(Bmc3G_Map_t) + (double)nBytes) ) return 0;
    pMap = ABC_CALLOC( Bmc3G_Map_t, 1 );
    if ( p->pPars->nQueries )
    {
        pMap->pLits = ABC_FALLOC( int, p->nMapEntries );
        pMap->pLits[0] = 0;
    }
    else
    {
        pMap->pBits = ABC_FALLOC( unsigned char, nBytes );
        pMap->pBits[0] &= ~3;
    }
    Vec_PtrPush( p->vMaps, pMap );
    p->nMapBytes += sizeof(Bmc3G_Map_t) + nBytes;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Indexes the sequential cone of the property outputs.]

  Description [The per-frame maps omit objects outside this cone.
  The original input and register order is retained for trace validation.]

  SideEffects [Creates the shared object-to-map index.]

  SeeAlso     [Bmc3G_Unroll]

***********************************************************************/
static void Bmc3G_IndexCone( Bmc3G_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, Id, Count = 0;
    p->vMapIds = Vec_IntStartFull( Gia_ManObjNum(p->pGia) );
    Vec_IntWriteEntry( p->vMapIds, 0, 0 );
    p->nMapEntries = 1;
    Gia_ManForEachPo( p->pGia, pObj, i )
        Vec_IntPush( p->vStack, Gia_ObjFaninId0p(p->pGia, pObj) );
    while ( Vec_IntSize(p->vStack) )
    {
        if ( !(Count++ & 1023) && Bmc3G_Stop(p) ) return;
        Id = Vec_IntPop( p->vStack );
        if ( Vec_IntEntry(p->vMapIds, Id) >= 0 ) continue;
        Vec_IntWriteEntry( p->vMapIds, Id, p->nMapEntries++ );
        pObj = Gia_ManObj( p->pGia, Id );
        if ( Gia_ObjIsAnd(pObj) )
            Vec_IntPushTwo( p->vStack, Gia_ObjFaninId0(pObj, Id), Gia_ObjFaninId1(pObj, Id) );
        else if ( Gia_ObjIsRo(p->pGia, pObj) )
            Vec_IntPush( p->vStack, Gia_ObjFaninId0p(p->pGia, Gia_ObjRoToRi(p->pGia, pObj)) );
    }
}

/**Function*************************************************************

  Synopsis    [Flattens a conjunction or a disjunction into literals.]

  Description [Unexpanded subgraphs remain literals when the limit is reached.
  A repeated subgraph has the same polarity inside one flattened operator.]

  SideEffects [Uses traversal IDs on the private graph.]

  SeeAlso     [Bmc3G_SplitProperty]

***********************************************************************/
static void Bmc3G_CollectTerms( Gia_Man_t * pGia, int Lit, int fOr, int Limit, Vec_Int_t * vWork, Vec_Int_t * vTerms )
{
    Gia_Obj_t * pObj;
    Vec_IntClear( vWork );
    Vec_IntClear( vTerms );
    Vec_IntPush( vWork, Lit );
    Gia_ManIncrementTravId( pGia );
    while ( Vec_IntSize(vWork) )
    {
        Lit = Vec_IntPop( vWork );
        pObj = Gia_ManObj( pGia, Abc_Lit2Var(Lit) );
        if ( Gia_ObjIsAnd(pObj) && Abc_LitIsCompl(Lit) == fOr )
        {
            if ( Gia_ObjIsTravIdCurrent(pGia, pObj) ) continue;
            if ( Vec_IntSize(vWork) + Vec_IntSize(vTerms) + 1 < Limit )
            {
                Gia_ObjSetTravIdCurrent( pGia, pObj );
                Vec_IntPushTwo( vWork, Gia_ObjFaninLit0p(pGia, pObj) ^ fOr, Gia_ObjFaninLit1p(pGia, pObj) ^ fOr );
                continue;
            }
        }
        Vec_IntPushUnique( vTerms, Lit );
    }
}

/**Function*************************************************************

  Synopsis    [Splits a large disjunction below a property's Boolean guards.]

  Description [Searches a bounded number of alternating AND and OR levels.
  Above the chosen disjunction D the property has the form R | (G & D).
  An AND sibling restricts both R and G, while an OR sibling extends R.
  The outputs R and G & D_i therefore cover the exact original property.
  The input order and the register transition functions are preserved.]

  SideEffects [Uses traversal IDs and Value on the private input.]

  SeeAlso     [Bmc_GiaReduceIso]

***********************************************************************/
static Gia_Man_t * Bmc3G_SplitProperty( Gia_Man_t * pGia, int (*pFuncStop)(void *), void * pData )
{
    Gia_Man_t * pNew = NULL;
    Gia_Obj_t * pObj;
    Vec_Int_t * vLits = Vec_IntAlloc( 64 ), * vParents = Vec_IntAlloc( 64 );
    Vec_Int_t * vTerms = Vec_IntAlloc( 32 ), * vBest = Vec_IntAlloc( 32 ), * vWork = Vec_IntAlloc( 32 );
    int i, k, Level, End, Lit, Child, Rest, fOr, Best = -1, Guard = 1, Residual = 0;
    Vec_IntPush( vLits, Gia_ObjFaninLit0p(pGia, Gia_ManPo(pGia, 0)) );
    Vec_IntPush( vParents, -1 );
    for ( i = Level = 0; Level < 5 && i < Vec_IntSize(vLits); Level++ )
    {
        End = Vec_IntSize(vLits);
        for ( ; i < End; i++ )
        {
            if ( (pFuncStop && pFuncStop(pData)) ) goto finish;
            Lit = Vec_IntEntry( vLits, i );
            if ( !Gia_ObjIsAnd(Gia_ManObj(pGia, Abc_Lit2Var(Lit))) ) continue;
            fOr = Abc_LitIsCompl( Lit );
            Bmc3G_CollectTerms( pGia, Lit, fOr, fOr ? 512 : 64, vWork, vTerms );
            if ( fOr && Vec_IntSize(vTerms) >= 8 )
            {
                if ( Vec_IntSize(vBest) < Vec_IntSize(vTerms) )
                {
                    Vec_IntClear( vBest );
                    Vec_IntAppend( vBest, vTerms );
                    Best = i;
                }
                continue;
            }
            if ( Level == 4 ) continue;
            Vec_IntForEachEntry( vTerms, Child, k )
            {
                if ( Vec_IntSize(vLits) >= 192 ) break;
                if ( !Gia_ObjIsAnd(Gia_ManObj(pGia, Abc_Lit2Var(Child))) || Vec_IntFind(vLits, Child) >= 0 )
                    continue;
                Vec_IntPush( vLits, Child );
                Vec_IntPush( vParents, i );
            }
        }
    }
    if ( Best < 0 || (pFuncStop && pFuncStop(pData)) ) goto finish;
    pNew = Gia_ManStart( Gia_ManObjNum(pGia) + 2 * Vec_IntSize(vBest) + 64 );
    pNew->pName = Abc_UtilStrsav( pGia->pName );
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(pGia)->Value = 0;
    Gia_ManForEachCi( pGia, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( pGia, pObj, i )
    {
        if ( !(i & 1023) && (pFuncStop && pFuncStop(pData)) ) { Gia_ManStopP(&pNew); goto finish; }
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    }
    while ( Vec_IntEntry(vParents, Best) >= 0 )
    {
        Child = Vec_IntEntry( vLits, Best );
        Best = Vec_IntEntry( vParents, Best );
        Lit = Vec_IntEntry( vLits, Best );
        fOr = Abc_LitIsCompl( Lit );
        Bmc3G_CollectTerms( pGia, Lit, fOr, fOr ? 512 : 64, vWork, vTerms );
        Rest = 1;
        Vec_IntForEachEntry( vTerms, Lit, i )
            if ( Lit != Child )
                Rest = Gia_ManHashAnd( pNew, Rest, Gia_ObjLitCopy(pGia, Lit) ^ fOr );
        if ( fOr )
            Residual = Gia_ManHashOr( pNew, Residual, Abc_LitNot(Rest) );
        else
        {
            Guard = Gia_ManHashAnd( pNew, Guard, Rest );
            Residual = Gia_ManHashAnd( pNew, Residual, Rest );
        }
    }
    Vec_IntForEachEntry( vBest, Lit, i )
        Vec_IntWriteEntry( vBest, i, Gia_ManHashAnd(pNew, Guard, Gia_ObjLitCopy(pGia, Lit)) );
    if ( Residual ) Gia_ManAppendCo( pNew, Residual );
    Vec_IntForEachEntry( vBest, Lit, i )
        Gia_ManAppendCo( pNew, Lit );
    Gia_ManForEachRi( pGia, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(pGia) );
    Gia_ManHashStop( pNew );
finish:
    Vec_IntFree( vLits );
    Vec_IntFree( vParents );
    Vec_IntFree( vTerms );
    Vec_IntFree( vBest );
    Vec_IntFree( vWork );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Keeps representatives of structurally isomorphic sequential properties.]

  Description [Identical canonical AIGER records include the full transition
  relation of both cones, with registers and their next-state functions
  permuted together. Such properties have witnesses at the same depths.
  The representative model retains the original PI order. Its PO indices
  map to the initial outputs or, after splitting, to the single initial PO.]

  SideEffects [Uses traversal IDs and Value on the private model.]

  SeeAlso     [Bmc3G_SplitProperty]

***********************************************************************/
Gia_Man_t * Bmc_GiaReduceIso( Gia_Man_t * pGia, Vec_Int_t ** pvPos, int nMemoryLimit,
    int (*pFuncStop)(void *), void * pData, int fVerbose )
{
    Gia_Man_t * pSplit, * pPart, * pCanon, * pResult = NULL;
    Vec_Ptr_t * vKeys;
    Vec_Int_t * vReps;
    Vec_Str_t * vKey, * vOther, * vSeen;
    abctime Stop = Abc_Clock() + CLOCKS_PER_SEC;
    int i, k, Lit, nPartAnds, nRepAndMax = 0, nObjs, fSplit;
    if ( !pvPos ) return NULL;
    *pvPos = NULL;
    if ( !pGia || Gia_ManConstrNum(pGia) || pGia->pMuxes || Gia_ManXorNum(pGia) ||
         Gia_ManBufNum(pGia) || Gia_ManHasChoices(pGia) || Gia_ManBoxNum(pGia) ||
         (pGia->vRegInits && (Vec_IntSize(pGia->vRegInits) != Gia_ManRegNum(pGia) ||
          Vec_IntCountEntry(pGia->vRegInits, 0) != Gia_ManRegNum(pGia))) ) return NULL;
    nObjs = Gia_ManObjNum( pGia );
    fSplit = Gia_ManPoNum(pGia) == 1;
    if ( !Gia_ManPoNum(pGia) || !Gia_ManRegNum(pGia) || nObjs > 200000 ||
         (nMemoryLimit && 24.0 + 0.00025 * nObjs >= nMemoryLimit) ) return NULL;
    pSplit = fSplit ? Bmc3G_SplitProperty(pGia, pFuncStop, pData) : pGia;
    if ( !pSplit ) return NULL;
    vKeys = Vec_PtrAlloc( 16 );
    vReps = Vec_IntAlloc( 16 );
    vSeen = Vec_StrStart( 2 * Gia_ManObjNum(pSplit) );
    if ( Gia_ManLevelNum(pSplit) > (fSplit ? 512 : 1024) ) goto finish;
    for ( i = 0; i < Gia_ManPoNum(pSplit); i++ )
    {
        if ( (pFuncStop && pFuncStop(pData)) ) goto finish;
        Lit = Gia_ObjFaninLit0p( pSplit, Gia_ManPo(pSplit, i) );
        if ( Vec_StrEntry(vSeen, Lit) ) continue;
        Vec_StrWriteEntry( vSeen, Lit, 1 );
        if ( Abc_Clock() >= Stop )
        {
            if ( fSplit ) goto finish;
            Vec_IntPush( vReps, i );
            continue;
        }
        pPart = Gia_ManDupCones( pSplit, &i, 1, 1 );
        if ( Gia_ManObjNum(pPart) > 8192 )
        {
            Gia_ManStop( pPart );
            if ( fSplit ) goto finish;
            Vec_IntPush( vReps, i );
            continue;
        }
        nPartAnds = Gia_ManAndNum( pPart );
        // The first distinct literal is always retained. Its cone alone
        // can already rule out the required reduction in total AND count.
        if ( fSplit && !Vec_IntSize(vReps) && 4 * nPartAnds > 3 * Gia_ManAndNum(pGia) )
        {
            Gia_ManStop( pPart );
            goto finish;
        }
        pCanon = Gia_ManIsoCanonicize( pPart, 0 );
        vKey = Gia_AigerWriteIntoMemoryStr( pCanon );
        Gia_ManStop( pCanon );
        Gia_ManStop( pPart );
        Vec_PtrForEachEntry( Vec_Str_t *, vKeys, vOther, k )
            if ( Vec_StrCompareVec(vKey, vOther) == 0 ) break;
        if ( k < Vec_PtrSize(vKeys) ) Vec_StrFree( vKey );
        else
        {
            Vec_PtrPush( vKeys, vKey );
            Vec_IntPush( vReps, i );
            // Every retained cone is present in the final representative AIG.
            nRepAndMax = Abc_MaxInt( nRepAndMax, nPartAnds );
            if ( fSplit && (2 * Vec_IntSize(vReps) > Gia_ManPoNum(pSplit) ||
                 4 * nRepAndMax > 3 * Gia_ManAndNum(pGia) ||
                 (ABC_INT64_T)nRepAndMax * Vec_IntSize(vReps) > Gia_ManAndNum(pGia)) )
                goto finish;
        }
    }
    if ( Vec_IntSize(vReps) == Gia_ManPoNum(pSplit) || (pFuncStop && pFuncStop(pData)) ) goto finish;
    if ( fSplit && 2 * Vec_IntSize(vReps) > Gia_ManPoNum(pSplit) ) goto finish;
    pResult = Gia_ManDupCones( pSplit, Vec_IntArray(vReps), Vec_IntSize(vReps), 0 );
    // Splitting a single property introduces a query per representative in each frame.
    if ( fSplit && (4 * Gia_ManAndNum(pResult) > 3 * Gia_ManAndNum(pGia) ||
         (ABC_INT64_T)Vec_IntSize(vReps) * Gia_ManAndNum(pResult) > Gia_ManAndNum(pGia)) )
        Gia_ManStopP( &pResult );
    if ( pResult && fVerbose )
        Abc_Print( 1, "BMC symmetry: %d %s, %d representatives, %d -> %d ANDs.\n",
            Gia_ManPoNum(pSplit), fSplit ? "disjuncts" : "outputs", Vec_IntSize(vReps),
            Gia_ManAndNum(pGia), Gia_ManAndNum(pResult) );
    if ( pResult )
    {
        if ( fSplit ) Vec_IntFill( vReps, Vec_IntSize(vReps), 0 );
        *pvPos = vReps;
        vReps = NULL;
    }
finish:
    Vec_StrFree( vSeen );
    Vec_PtrForEachEntry( Vec_Str_t *, vKeys, vKey, i ) Vec_StrFree( vKey );
    Vec_PtrFree( vKeys );
    Vec_IntFreeP( &vReps );
    if ( fSplit ) Gia_ManStop( pSplit );
    return pResult;
}

/**Function*************************************************************

  Synopsis    [Checks the separate time allowance for preprocessing.]

  Description []

  SideEffects [Only a stop requested by the outer run ends the main search.]

  SeeAlso     [Bmc3G_Prepare]

***********************************************************************/
static int Bmc3G_PrepStop( void * pData )
{
    Bmc3G_Man_t * p = (Bmc3G_Man_t *)pData;
    return Bmc3G_Stop(p) || Abc_Clock() >= p->PrepDeadline;
}

/**Function*************************************************************

  Synopsis    [Sweeps redundant registers and rewrites the transition relation.]

  Description [Both steps preserve PI and PO order. Keeps each completed
  step that removes registers or ANDs. The two steps share a time budget.]

  SideEffects [Retains the original model for counterexample replay.]

  SeeAlso     [Bmc3G_Start Bmc3G_Cex]

***********************************************************************/
static void Bmc3G_Prepare( Bmc3G_Man_t * p )
{
    Gia_Man_t * pNext;
    abctime Start = Abc_Clock();
    int i, nAnds = Gia_ManAndNum(p->pGia), nRegs = Gia_ManRegNum(p->pGia);
    if ( !nRegs || (p->pPars->nMemoryLimit &&
         p->pPars->MemoryPeakMB + 256.0 * Gia_ManObjNum(p->pGia) / (1 << 20) >= p->pPars->nMemoryLimit) )
        return;
    p->PrepDeadline = Start + 2 * (abctime)CLOCKS_PER_SEC;
    for ( i = 0; i < 2 && !Bmc3G_PrepStop(p); i++ )
    {
        pNext = i ? Drw_ManRwsatWithStop(p->pGia, 0, 0, Bmc3G_PrepStop, p) :
                    Gia_ManSeqStructSweepWithStop(p->pGia, 1, 1, 0, Bmc3G_PrepStop, p);
        if ( !pNext ) break;
        if ( Gia_ManPiNum(pNext) != Gia_ManPiNum(p->pGia) || Gia_ManPoNum(pNext) != Gia_ManPoNum(p->pGia) ||
             (Gia_ManAndNum(pNext) >= Gia_ManAndNum(p->pGia) && Gia_ManRegNum(pNext) >= Gia_ManRegNum(p->pGia)) )
        {
            Gia_ManStop( pNext );
            continue;
        }
        if ( p->pOriginal ) Gia_ManStop( p->pGia );
        else p->pOriginal = p->pGia;
        p->pGia = pNext;
    }
    if ( p->pPars->fVerbose )
        Abc_Print( 1, "BMC preprocessing: ANDs %d -> %d, registers %d -> %d, time=%.3f sec.\n",
            nAnds, Gia_ManAndNum(p->pGia), nRegs, Gia_ManRegNum(p->pGia), (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC );
}

/**Function*************************************************************

  Synopsis    [Allocates private unrolling and incremental solver state.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Bmc3G_Man_t * Bmc3G_Start( Gia_Man_t * pGia, Bmc_GiaPar_t * pPars, int fFixedTarget )
{
    Bmc3G_Man_t * p = ABC_CALLOC( Bmc3G_Man_t, 1 );
    p->pPars = pPars;
    p->Start = Abc_Clock();
    p->Deadline = pPars->nTimeOut ? p->Start + (abctime)pPars->nTimeOut * CLOCKS_PER_SEC : 0;
    if ( pPars->TimeToStop && (!p->Deadline || pPars->TimeToStop < p->Deadline) )
        p->Deadline = pPars->TimeToStop;
    if ( Gia_ManObjNum(pGia) >= (1 << 28) ) pPars->fMemoryLimit = p->fStopped = 1;
    if ( Bmc3G_Stop(p) || Bmc3G_CheckMemory(p, 64.0 * Gia_ManObjNum(pGia)) ) return p;
    p->pGia = Gia_ManDupNormalize( pGia, 1 );
    if ( !fFixedTarget && pPars->fUseIso && !pPars->pShared )
    {
        Gia_Man_t * pReduced = Bmc_GiaReduceIso( p->pGia, &p->vOriginalPos, pPars->nMemoryLimit,
            Bmc3G_Stop, p, pPars->fVerbose );
        if ( pReduced )
        {
            p->pOriginal = p->pGia;
            p->pGia = pReduced;
        }
        if ( p->fStopped ) return p;
    }
    if ( !fFixedTarget && pPars->fPreprocess && !pPars->pShared )
    {
        Bmc3G_Prepare( p );
        if ( Bmc3G_Stop(p) ) return p;
    }
    p->pFrames = Gia_ManStart( Gia_ManObjNum(p->pGia) );
    Gia_ManHashStart( p->pFrames );
    p->vMaps = Vec_PtrAlloc( 128 );
    p->vVars = Vec_IntAlloc( 1024 );
    p->vCopies = Vec_IntAlloc( 1024 );
    p->vCiMap = Vec_IntAlloc( 1024 );
    p->vRoots = Vec_IntAlloc( Gia_ManPoNum(p->pGia) );
    p->vStack = Vec_IntAlloc( 1024 );
    p->vWork = Vec_WrdAlloc( 1024 );
    Bmc3G_IndexCone( p );
    if ( p->fStopped ) return p;
    p->pSat = ccadical_init();
    ccadical_set_option( p->pSat, "quiet", 1 );
    // Avoid repeated elimination while adding circuit clauses incrementally.
    if ( !fFixedTarget )
    {
        ccadical_set_option( p->pSat, "inprocessing", 0 );
        ccadical_set_option( p->pSat, "fastelim", 0 );
        ccadical_set_option( p->pSat, "lucky", 0 );
    }
    ccadical_set_option( p->pSat, "phase", pPars->fPhase );
    if ( pPars->fEarlyActivity )
    {
        // Alternate focused and activity-based search, using glue-based restarts in both.
        ccadical_set_option( p->pSat, "stabilizeinit", 64 );
        ccadical_set_option( p->pSat, "reluctant", 0 );
        ccadical_set_option( p->pSat, "restartmarginstable", 10 );
        ccadical_set_option( p->pSat, "target", 0 );
        ccadical_set_option( p->pSat, "rephase", 0 );
        ccadical_set_option( p->pSat, "chrono", 0 );
    }
    // Poll the caller at each solver cancellation point.
    ccadical_set_option( p->pSat, "terminateint", 0 );
    ccadical_set_terminate( p->pSat, p, Bmc3G_Stop );
    p->nVars = 1;
    Vec_IntPush( p->vVars, 1 );
    ccadical_add( p->pSat, -1 );
    ccadical_add( p->pSat, 0 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Releases all state owned by one invocation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Bmc3G_StopManager( Bmc3G_Man_t * p )
{
    Bmc3G_Map_t * pMap;
    int i;
    if ( p->pSat ) ccadical_release( p->pSat );
    Gia_ManStopP( &p->pGia );
    Gia_ManStopP( &p->pFrames );
    Gia_ManStopP( &p->pOriginal );
    if ( p->vMaps )
    {
        Vec_PtrForEachEntry( Bmc3G_Map_t *, p->vMaps, pMap, i )
        {
            ABC_FREE( pMap->pLits );
            ABC_FREE( pMap->pBits );
            ABC_FREE( pMap );
        }
        Vec_PtrFree( p->vMaps );
    }
    Vec_IntFreeP( &p->vVars );
    Vec_IntFreeP( &p->vCopies );
    Vec_IntFreeP( &p->vCiMap );
    Vec_IntFreeP( &p->vRoots );
    Vec_IntFreeP( &p->vOriginalPos );
    Vec_IntFreeP( &p->vStack );
    Vec_WrdFreeP( &p->vWork );
    Vec_IntFreeP( &p->vMapIds );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Substitutes an unconditional solver assignment, when available.]

  Description [Only the solver's root assignments are queried. No temporary
  assumption or saved satisfying assignment is used as a constant.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc3G_Fixed( Bmc3G_Man_t * p, int Lit )
{
    int Id = Abc_Lit2Var(Lit), Var, Value;
    if ( Id == 0 || Id >= Vec_IntSize(p->vVars) ) return Lit;
    Var = Vec_IntEntry( p->vVars, Id );
    if ( !Var ) return Lit;
    Value = ccadical_fixed( p->pSat, Var );
    return Value ? (Value > 0) ^ Abc_LitIsCompl(Lit) : Lit;
}

/**Function*************************************************************

  Synopsis    [Unrolls a demanded cone without recursive C calls.]

  Description [Only unconditional SAT assignments are used as constants.
  Assumptions and incomplete search results never simplify future frames.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc3G_Unroll( Bmc3G_Man_t * p, int Id, int Frame )
{
    int Count = 0;
    Vec_WrdClear( p->vWork );
    Vec_WrdPush( p->vWork, ((word)(unsigned)Frame << 32) | (unsigned)Id );
    while ( Vec_WrdSize(p->vWork) )
    {
        word Entry = Vec_WrdEntryLast( p->vWork );
        int f = (int)(Entry >> 32), i = (int)(unsigned)Entry;
        Bmc3G_Map_t * pMap = (Bmc3G_Map_t *)Vec_PtrEntry( p->vMaps, f );
        Gia_Obj_t * pObj = Gia_ManObj( p->pGia, i );
        int Id0, Id1, Lit0, Lit1, Index = Vec_IntEntry(p->vMapIds, i), Index0, Index1;
        if ( !(Count++ & 1023) && Bmc3G_Stop(p) ) return -1;
        assert( Index >= 0 );
        if ( Bmc3G_MapRead(pMap, Index) >= 0 ) { Vec_WrdPop(p->vWork); continue; }
        if ( Gia_ObjIsPi(p->pGia, pObj) )
        {
            if ( !Bmc3G_MapWrite(p, pMap, Index, Gia_ManAppendCi(p->pFrames)) ) return -1;
            Vec_IntPushTwo( p->vCiMap, Gia_ObjCioId(pObj), f );
        }
        else if ( Gia_ObjIsRo(p->pGia, pObj) )
        {
            Gia_Obj_t * pRi = Gia_ObjRoToRi( p->pGia, pObj );
            Bmc3G_Map_t * pPrev = f ? (Bmc3G_Map_t *)Vec_PtrEntry(p->vMaps, f - 1) : NULL;
            Id0 = Gia_ObjFaninId0p( p->pGia, pRi );
            Index0 = Vec_IntEntry( p->vMapIds, Id0 );
            if ( f && Bmc3G_MapRead(pPrev, Index0) < 0 )
            {
                Vec_WrdPush( p->vWork, ((word)(unsigned)(f - 1) << 32) | (unsigned)Id0 );
                continue;
            }
            Lit0 = f ? Bmc3G_Fixed(p, Bmc3G_MapRead(pPrev, Index0)) ^ Gia_ObjFaninC0(pRi) : 0;
            if ( !f && p->fFreeInit )
                Lit0 = Gia_ManAppendCi( p->pFrames );
            if ( !Bmc3G_MapWrite(p, pMap, Index, Lit0) ) return -1;
        }
        else
        {
            assert( Gia_ObjIsAnd(pObj) );
            Id0 = Gia_ObjFaninId0( pObj, i );
            Id1 = Gia_ObjFaninId1( pObj, i );
            Index0 = Vec_IntEntry( p->vMapIds, Id0 );
            Index1 = Vec_IntEntry( p->vMapIds, Id1 );
            if ( Bmc3G_MapRead(pMap, Index0) < 0 )
            {
                Vec_WrdPush( p->vWork, ((word)(unsigned)f << 32) | (unsigned)Id0 );
                continue;
            }
            Lit0 = Bmc3G_Fixed(p, Bmc3G_MapRead(pMap, Index0)) ^ Gia_ObjFaninC0(pObj);
            if ( Lit0 == 0 ) { Bmc3G_MapWrite(p, pMap, Index, 0); continue; }
            if ( Bmc3G_MapRead(pMap, Index1) < 0 )
            {
                Vec_WrdPush( p->vWork, ((word)(unsigned)f << 32) | (unsigned)Id1 );
                continue;
            }
            Lit1 = Bmc3G_Fixed(p, Bmc3G_MapRead(pMap, Index1)) ^ Gia_ObjFaninC1(pObj);
            if ( !Bmc3G_MapWrite(p, pMap, Index, Gia_ManHashAnd(p->pFrames, Lit0, Lit1)) ) return -1;
        }
        Vec_WrdPop( p->vWork );
    }
    return Bmc3G_Fixed( p, Bmc3G_MapRead((Bmc3G_Map_t *)Vec_PtrEntry(p->vMaps, Frame),
                                      Vec_IntEntry(p->vMapIds, Id)) );
}

/**Function*************************************************************

  Synopsis    [Collects only logic not represented by an existing SAT variable.]

  Description [Mapped nodes become boundary inputs of the new CNF cone.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc3G_Collect( Bmc3G_Man_t * p, Gia_Man_t * pCone, int Id )
{
    int Count = 0;
    Vec_IntClear( p->vStack );
    Vec_IntPush( p->vStack, Id );
    while ( Vec_IntSize(p->vStack) )
    {
        int i = Vec_IntEntryLast(p->vStack), Id0, Id1, Lit;
        Gia_Obj_t * pObj = Gia_ManObj( p->pFrames, i );
        if ( !(Count++ & 1023) &&
             (Bmc3G_Stop(p) || Bmc3G_CheckMemory(p, 64.0 * pCone->nObjsAlloc)) ) return -1;
        if ( Vec_IntEntry(p->vCopies, i) >= 0 ) { Vec_IntPop(p->vStack); continue; }
        if ( Vec_IntEntry(p->vVars, i) || Gia_ObjIsCi(pObj) )
            Lit = Gia_ManAppendCi( pCone );
        else
        {
            assert( Gia_ObjIsAnd(pObj) );
            Id0 = Gia_ObjFaninId0( pObj, i );
            Id1 = Gia_ObjFaninId1( pObj, i );
            if ( Vec_IntEntry(p->vCopies, Id0) < 0 ) { Vec_IntPush(p->vStack, Id0); continue; }
            if ( Vec_IntEntry(p->vCopies, Id1) < 0 ) { Vec_IntPush(p->vStack, Id1); continue; }
            Lit = Gia_ManAppendAnd( pCone,
                Vec_IntEntry(p->vCopies, Id0) ^ Gia_ObjFaninC0(pObj),
                Vec_IntEntry(p->vCopies, Id1) ^ Gia_ObjFaninC1(pObj) );
        }
        Vec_IntWriteEntry( p->vCopies, i, Lit );
        Gia_ManObj(pCone, Abc_Lit2Var(Lit))->Value = i;
        Vec_IntPop( p->vStack );
    }
    return Vec_IntEntry( p->vCopies, Id );
}

/**Function*************************************************************

  Synopsis    [Adds a mapped CNF for the current frame to the same SAT solver.]

  Description [The boundary mapping survives solver inprocessing. CaDiCaL
  restores eliminated clauses when a later incremental clause needs them.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc3G_AddCnf( Bmc3G_Man_t * p )
{
    Gia_Man_t * pCone = Gia_ManStart( 1024 );
    Gia_Obj_t * pObj;
    Jf_Par_t Pars;
    Cnf_Dat_t * pCnf = NULL;
    int * pMap = NULL;
    int i, k, Root, Lit, Var, Result = 0;
    Vec_IntFillExtra( p->vVars, Gia_ManObjNum(p->pFrames), 0 );
    Vec_IntFillExtra( p->vCopies, Gia_ManObjNum(p->pFrames), -1 );
    Vec_IntWriteEntry( p->vCopies, 0, 0 );
    Vec_IntForEachEntry( p->vRoots, Root, i )
    {
        pObj = Gia_ManObj( p->pFrames, Root );
        Lit = Bmc3G_Collect( p, pCone, Gia_ObjFaninId0p(p->pFrames, pObj) );
        if ( Lit < 0 ) goto finish;
        Lit = Gia_ManAppendCo( pCone, Lit ^ Gia_ObjFaninC0(pObj) );
        Gia_ManObj(pCone, Abc_Lit2Var(Lit))->Value = Root;
    }
    if ( Bmc3G_Stop(p) ) goto finish;
    if ( Bmc3G_CheckMemory(p, 512.0 * Gia_ManObjNum(pCone)) ) goto finish;
    Mf_ManSetDefaultPars( &Pars );
    Pars.fGenCnf = Pars.fCnfObjIds = Pars.fCnfOnly = 1;
    Pars.fCoarsen = Pars.fAddOrCla = 0;
    Pars.nLutSize = p->pPars->nLutSize;
    // A small cut pool and one mapping pass keep incremental construction inexpensive.
    Pars.nCutNum = 4;
    Pars.nRounds = 1;
    Pars.nRoundsEla = 0;
    Mf_ManPerformMappingWithStop( pCone, &Pars, Bmc3G_Stop, p );
    pCnf = (Cnf_Dat_t *)pCone->pData;
    if ( !pCnf || Bmc3G_Stop(p) ) goto finish;
    p->nCnfLits += pCnf->nLiterals;
    pMap = ABC_FALLOC( int, Gia_ManObjNum(pCone) );
    pMap[0] = 1;
    Gia_ManForEachObj1( pCone, pObj, i )
    {
        if ( !(i & 1023) && Bmc3G_Stop(p) ) goto finish;
        if ( pCnf->pObj2Count[i] <= 0 && !Gia_ObjIsCi(pObj) ) continue;
        Var = Vec_IntEntry( p->vVars, pObj->Value );
        if ( !Var )
        {
            if ( p->nVars == INT_MAX - 1 ) { p->fStopped = 1; goto finish; }
            Vec_IntWriteEntry( p->vVars, pObj->Value, (Var = ++p->nVars) );
        }
        pMap[i] = Var;
    }
    ccadical_resize( p->pSat, p->nVars );
    for ( i = 0; i < pCnf->nClauses; i++ )
    {
        if ( !(i & 1023) && Bmc3G_Stop(p) ) goto finish;
        for ( k = 0; k < pCnf->pClauses[i+1] - pCnf->pClauses[i]; k++ )
        {
            Lit = pCnf->pClauses[i][k];
            Var = pMap[Abc_Lit2Var(Lit)];
            assert( Var > 0 );
            ccadical_add( p->pSat, Abc_LitIsCompl(Lit) ? -Var : Var );
        }
        ccadical_add( p->pSat, 0 );
    }
    Result = 1;
finish:
    Gia_ManForEachObj( pCone, pObj, i )
        Vec_IntWriteEntry( p->vCopies, pObj->Value, -1 );
    Cnf_DataFree( pCnf );
    ABC_FREE( pMap );
    Gia_ManStop( pCone );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Builds and verifies a concrete counterexample on the private input.]

  Description [Unconstrained input bits are zero. A completed SAT hit is
  verified even if the search deadline or allocation estimate was reached.
  Counterexample storage is bounded by its integer-indexed representation.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Abc_Cex_t * Bmc3G_Cex( Bmc3G_Man_t * p, int Frame, int Output, int fModel )
{
    Gia_Obj_t * pObj;
    Abc_Cex_t * pCex;
    int i, Var, Pi, f, nPis = Gia_ManPiNum(p->pGia), nRegs = Gia_ManRegNum(p->pGia);
    if ( (ABC_INT64_T)(Frame + 1) * nPis + nRegs > INT_MAX - 32 ) return NULL;
    pCex = Abc_CexAlloc( nRegs, nPis, Frame + 1 );
    pCex->iFrame = Frame;
    pCex->iPo = Output;
    if ( fModel )
        Gia_ManForEachPi( p->pFrames, pObj, i )
        {
            // A previous probe can have introduced inputs beyond this witness.
            f = Vec_IntEntry( p->vCiMap, 2*i + 1 );
            if ( f > Frame ) continue;
            Var = Vec_IntEntry( p->vVars, Gia_ObjId(p->pFrames, pObj) );
            if ( Var <= 0 || ccadical_val(p->pSat, Var) <= 0 ) continue;
            Pi = Vec_IntEntry( p->vCiMap, 2*i );
            Abc_InfoSetBit( pCex->pData, nRegs + f*nPis + Pi );
        }
    if ( Gia_ManVerifyCex(p->pGia, pCex, 0) ) return pCex;
    Abc_Print( 1, "Warning: &bmc3 rejected a counterexample from CaDiCaL.\n" );
    Abc_CexFree( pCex );
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Checks supported inputs and their initial state.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Bmc3G_CheckInput( Gia_Man_t * pGia, Bmc_GiaPar_t * pPars )
{
    int i, Init;
    if ( !pGia || !pPars || pPars->nFramesMax < 0 || pPars->nFramesMax >= INT_MAX ||
         pPars->nTimeOut < 0 || pPars->nTimeOut > 86400 || pPars->nConfLimit < 0 ||
         pPars->nFramesJump < 0 || pPars->nFramesJump >= INT_MAX ||
         pPars->nMemoryLimit < 0 || pPars->nMemoryLimit > (1 << 20) ||
         (pPars->fPhase != 0 && pPars->fPhase != 1) ||
         (pPars->fEarlyActivity != 0 && pPars->fEarlyActivity != 1) ||
         (pPars->fTernaryPrefix != 0 && pPars->fTernaryPrefix != 1) ||
         (pPars->fUseIso != 0 && pPars->fUseIso != 1) ||
         (pPars->fWindowProof != 0 && pPars->fWindowProof != 1) ||
         pPars->nLutSize < 3 || pPars->nLutSize > 9 || Gia_ManConstrNum(pGia) ||
         Gia_ManHasChoices(pGia) || pGia->pMuxes || Gia_ManXorNum(pGia) ||
         Gia_ManBufNum(pGia) || Gia_ManBoxNum(pGia) ) return 0;
    if ( pGia->vRegInits )
    {
        if ( Vec_IntSize(pGia->vRegInits) != Gia_ManRegNum(pGia) ) return 0;
        Vec_IntForEachEntry( pGia->vRegInits, Init, i )
            if ( Init != 0 ) return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Propagates constants before constructing the initial frame cones.]

  Description [Every primary input is unknown. Only values forced by the zero
  initial state and earlier unconditional constants are saved. Simulation ends
  after the first SAT query, retaining lazy construction for the remaining run.]

  SideEffects [Fills constant entries in the current compact map.]

  SeeAlso     [Bmc3G_Unroll]

***********************************************************************/
static void Bmc3G_PropagateConstants( Bmc3G_Man_t * p, int Frame )
{
    Bmc3G_Map_t * pMap = (Bmc3G_Map_t *)Vec_PtrEntry( p->vMaps, Frame );
    Bmc3G_Map_t * pPrev = Frame ? (Bmc3G_Map_t *)Vec_PtrEntry( p->vMaps, Frame - 1 ) : NULL;
    Gia_Obj_t * pObj, * pRi;
    int i, Index, Index0, Index1, Lit0, Lit1;
    Gia_ManForEachRo( p->pGia, pObj, i )
    {
        if ( !(i & 1023) && Bmc3G_Stop(p) ) return;
        Index = Vec_IntEntry( p->vMapIds, Gia_ObjId(p->pGia, pObj) );
        if ( Index < 0 ) continue;
        Lit0 = 0;
        if ( Frame )
        {
            pRi = Gia_ObjRoToRi( p->pGia, pObj );
            Index0 = Vec_IntEntry( p->vMapIds, Gia_ObjFaninId0p(p->pGia, pRi) );
            Lit0 = Bmc3G_MapRead( pPrev, Index0 );
            if ( Lit0 < 0 || Lit0 > 1 ) continue;
            Lit0 ^= Gia_ObjFaninC0(pRi);
        }
        Bmc3G_MapWrite( p, pMap, Index, Lit0 );
    }
    Gia_ManForEachAnd( p->pGia, pObj, i )
    {
        if ( !(i & 1023) && Bmc3G_Stop(p) ) return;
        Index = Vec_IntEntry( p->vMapIds, i );
        if ( Index < 0 ) continue;
        Index0 = Vec_IntEntry( p->vMapIds, Gia_ObjFaninId0(pObj, i) );
        Index1 = Vec_IntEntry( p->vMapIds, Gia_ObjFaninId1(pObj, i) );
        Lit0 = Bmc3G_MapRead( pMap, Index0 );
        Lit1 = Bmc3G_MapRead( pMap, Index1 );
        if ( Lit0 >= 0 && Lit0 <= 1 ) Lit0 ^= Gia_ObjFaninC0(pObj);
        if ( Lit1 >= 0 && Lit1 <= 1 ) Lit1 ^= Gia_ObjFaninC1(pObj);
        if ( Lit0 == 0 || Lit1 == 0 ) Bmc3G_MapWrite( p, pMap, Index, 0 );
        else if ( Lit0 == 1 && Lit1 == 1 ) Bmc3G_MapWrite( p, pMap, Index, 1 );
    }
}

/**Function*************************************************************

  Synopsis    [Records a newly certified range of consecutive frames.]

  Description [An event-driven prefix can be ahead of the concrete maps.]

  SideEffects [Advances the safe prefix monotonically.]

  SeeAlso     [Bmc3G_EventPrefix]

***********************************************************************/
static void Bmc3G_RecordFrames( Bmc3G_Man_t * p, int Frame, int nFrames )
{
    if ( Frame < p->pPars->nFramesDone ) return;
    assert( nFrames > 0 && Frame + 1 - nFrames == p->pPars->nFramesDone );
    p->pPars->nFramesDone = Frame + 1;
    if ( p->pPars->fVerbose )
        Abc_Print( 1, "%4d + : Var = %d. Cla = %llu. Conf = %d. Time = %.3f sec\n",
            Frame, p->nVars, (unsigned long long)ccadical_live_clauses(p->pSat), ccadical_conflicts(p->pSat),
            (double)(Abc_Clock() - p->Start) / CLOCKS_PER_SEC );
}

/**Function*************************************************************

  Synopsis    [Evaluates an AND or output over zero, one and unknown.]

  Description []

  SideEffects []

  SeeAlso     [Bmc3G_EventPrefix]

***********************************************************************/
static inline int Bmc3G_TernaryValue( Gia_Obj_t * pObj, int Id, unsigned char * pValues )
{
    int A = pValues[Gia_ObjFaninId0(pObj, Id)], B;
    if ( A < 2 ) A ^= Gia_ObjFaninC0(pObj);
    if ( Gia_ObjIsCo(pObj) || A == 0 ) return A;
    B = pValues[Gia_ObjFaninId1(pObj, Id)];
    if ( B < 2 ) B ^= Gia_ObjFaninC1(pObj);
    return B == 0 ? 0 : Abc_MaxInt(A, B);
}

/**Function*************************************************************

  Synopsis    [Schedules changed fanouts in topological object order.]

  Description [One bit per object coalesces multiple changes to its inputs.
  A second level skips blocks of 64 objects that have no pending changes.]

  SideEffects []

  SeeAlso     [Bmc3G_EventPrefix]

***********************************************************************/
static inline void Bmc3G_ScheduleFanouts( Gia_Man_t * pGia, int Id, word * pWords, word * pPages )
{
    int Fan, i;
    Gia_ObjForEachFanoutStaticId( pGia, Id, Fan, i )
    {
        Abc_TtSetBit( pWords, Fan );
        Abc_TtSetBit( pPages, Fan >> 6 );
    }
}

/**Function*************************************************************

  Synopsis    [Certifies frames using ternary simulation with unknown primary inputs.]

  Description [Starts from register constants already established by unrolling.
  Each simulated cube covers every reachable state at that depth. A repeated
  cube closes a safe cycle. A nonzero or unknown output returns control to
  concrete BMC with all preceding certified frames retained. Only changed
  gates are evaluated after initialization. Brent's cycle detection uses one
  saved register cube, with an incremental count of its differing entries.]

  SideEffects [Advances the safe prefix. Returns one for a complete proof.]

  SeeAlso     [Bmc3G_PropagateConstants]

***********************************************************************/
static int Bmc3G_EventPrefix( Bmc3G_Man_t * p, int Frame, int Limit )
{
    Gia_Man_t * pGia = p->pGia;
    Gia_Obj_t * pObj;
    Bmc3G_Map_t * pMap = (Bmc3G_Map_t *)Vec_PtrEntry( p->vMaps, Frame );
    int nObjs = Gia_ManObjNum(pGia), nWords = Abc_Bit6WordNum(nObjs), nPages = Abc_Bit6WordNum(nWords);
    int i, k, Id, Ro, Reg, Index, Value, nDiff = 0, Length = 0, Power = 1, nBad = 0, fProof = 0;
    int Checkpoint = Frame;
    unsigned Visits = 0;
    word Extra = (word)48 * nObjs;
    unsigned char * pValues, * pSaved;
    word * pWords, * pPages;
    Vec_Int_t * vRis;
    // Static fanout construction is one linear pass without cancellation.
    if ( nObjs > (1 << 20) || (p->pPars->nMemoryLimit &&
         p->pPars->MemoryPeakMB + 1.25 * Extra / (1 << 20) >= p->pPars->nMemoryLimit) ) return 0;
    p->nMapBytes += Extra;
    Gia_ManStaticFanoutStart( pGia );
    pValues = ABC_CALLOC( unsigned char, nObjs );
    pSaved = ABC_ALLOC( unsigned char, Gia_ManRegNum(pGia) );
    pWords = ABC_CALLOC( word, nWords );
    pPages = ABC_CALLOC( word, nPages );
    vRis = Vec_IntAlloc( Gia_ManRegNum(pGia) );
    Gia_ManForEachObj1( pGia, pObj, Id )
    {
        if ( !(Id & 1023) && Bmc3G_Stop(p) ) goto finish;
        if ( Gia_ObjIsCi(pObj) )
        {
            Value = 2;
            if ( Gia_ObjIsRo(pGia, pObj) )
            {
                Index = Vec_IntEntry( p->vMapIds, Id );
                if ( Index >= 0 ) Value = Bmc3G_MapRead( pMap, Index );
                if ( Value != 0 && Value != 1 ) Value = 2;
                pSaved[Gia_ObjCioId(pObj) - Gia_ManPiNum(pGia)] = (unsigned char)Value;
            }
        }
        else
        {
            Value = Bmc3G_TernaryValue( pObj, Id, pValues );
            if ( Gia_ObjIsRi(pGia, pObj) ) Vec_IntPush( vRis, Id );
            if ( Gia_ObjIsPo(pGia, pObj) ) nBad += Value != 0;
        }
        pValues[Id] = (unsigned char)Value;
    }
    while ( Frame < Limit && !nBad && !Bmc3G_Stop(p) )
    {
        Bmc3G_RecordFrames( p, Frame++, 1 );
        Vec_IntForEachEntry( vRis, Id, i )
        {
            if ( !(++Visits & 1023) && Bmc3G_Stop(p) ) goto finish;
            pObj = Gia_ManObj( pGia, Id );
            Reg = Gia_ObjCioId(pObj) - Gia_ManPoNum(pGia);
            Ro = Gia_ObjId( pGia, Gia_ManRo(pGia, Reg) );
            if ( pValues[Ro] == pValues[Id] ) continue;
            nDiff += (pValues[Id] != pSaved[Reg]) - (pValues[Ro] != pSaved[Reg]);
            pValues[Ro] = pValues[Id];
            Bmc3G_ScheduleFanouts( pGia, Ro, pWords, pPages );
        }
        if ( !nDiff ) { fProof = 1; break; }
        if ( Frame == Limit ) break;
        if ( ++Length == Power )
        {
            Gia_ManForEachRo( pGia, pObj, i )
            {
                if ( !(++Visits & 1023) && Bmc3G_Stop(p) ) goto finish;
                pSaved[i] = pValues[Gia_ObjId(pGia, pObj)];
            }
            if ( Power <= INT_MAX / 2 ) Power *= 2;
            Length = nDiff = 0;
            Checkpoint = Frame;
        }
        Vec_IntClear( vRis );
        for ( k = 0; k < nPages; k++ )
            while ( pPages[k] )
            {
                int Block = 64 * k + Abc_Tt6FirstBit(pPages[k]);
                while ( pWords[Block] )
                {
                    if ( !(++Visits & 1023) && Bmc3G_Stop(p) ) goto finish;
                    Id = 64 * Block + Abc_Tt6FirstBit(pWords[Block]);
                    pWords[Block] &= pWords[Block] - 1;
                    pObj = Gia_ManObj( pGia, Id );
                    Value = Bmc3G_TernaryValue( pObj, Id, pValues );
                    if ( pValues[Id] == Value ) continue;
                    if ( Gia_ObjIsAnd(pObj) ) Bmc3G_ScheduleFanouts( pGia, Id, pWords, pPages );
                    else if ( Gia_ObjIsRi(pGia, pObj) ) Vec_IntPush( vRis, Id );
                    else nBad += (Value != 0) - (pValues[Id] != 0);
                    pValues[Id] = (unsigned char)Value;
                }
                pPages[k] &= pPages[k] - 1;
            }
    }
finish:
    if ( fProof && p->pPars->fVerbose )
        Abc_Print( 1, "BMC ternary simulation closed a safe cycle from frame %d to %d.\n", Checkpoint, Frame );
    Vec_IntFree( vRis );
    ABC_FREE( pValues );
    ABC_FREE( pSaved );
    ABC_FREE( pWords );
    ABC_FREE( pPages );
    Gia_ManStaticFanoutStop( pGia );
    p->nMapBytes -= Extra;
    return fProof;
}


/**Function*************************************************************

  Synopsis    [Checks a property after a bounded number of arbitrary-state transitions.]

  Description [All earlier frames from reset must already be safe. Every
  reachable state at any later frame has a predecessor Depth steps earlier.
  Refuting the disjunction of outputs after Depth steps from arbitrary state
  therefore proves safety. A satisfiable or interrupted query is inconclusive.]

  SideEffects [Accounts for the auxiliary solver in the caller's statistics.]

  SeeAlso     [Bmc3G_Unroll Bmc3G_AddCnf]

***********************************************************************/
static int Bmc3G_WindowProof( Bmc3G_Man_t * p, int Depth )
{
    Bmc_GiaPar_t Pars;
    Bmc3G_Man_t * pFree;
    Gia_Obj_t * pObj;
    int i, Lit, Root, Bad = 0, Status, Result = 0;
    abctime Start = Abc_Clock(), clk;
    double Used = p->pPars->MemoryPeakMB;
    if ( p->pPars->nMemoryLimit && Used + 64 >= p->pPars->nMemoryLimit ) return 0;
    Bmc_GiaSetDefaultParams( &Pars );
    Pars.nLutSize = p->pPars->nLutSize;
    Pars.nMemoryLimit = p->pPars->nMemoryLimit ? Abc_MinInt(2048, p->pPars->nMemoryLimit - (int)Used - 1) : 2048;
    Pars.TimeToStop = Start + 6 * CLOCKS_PER_SEC;
    // Limit the auxiliary cost when the reachable prefix needed no SAT calls.
    if ( !p->pPars->nQueries && Start - p->Start + CLOCKS_PER_SEC / 10 < Pars.TimeToStop - Start )
        Pars.TimeToStop = Start + (Start - p->Start) + CLOCKS_PER_SEC / 10;
    Pars.pFuncStop = Bmc3G_Stop;
    Pars.pStopData = p;
    pFree = Bmc3G_Start( p->pGia, &Pars, 0 );
    if ( pFree->fStopped ) goto finish;
    pFree->fFreeInit = 1;
    for ( i = 0; i <= Depth; i++ )
        if ( !Bmc3G_MapStart(pFree) ) goto finish;
    Gia_ManForEachPo( pFree->pGia, pObj, i )
    {
        if ( Bmc3G_Stop(pFree) ) goto finish;
        Lit = Bmc3G_Unroll( pFree, Gia_ObjFaninId0p(pFree->pGia, pObj), Depth );
        if ( Lit < 0 ) goto finish;
        Bad = Gia_ManHashOr( pFree->pFrames, Bad, Lit ^ Gia_ObjFaninC0(pObj) );
        if ( Bad == 1 ) goto finish;
    }
    if ( !Bad ) { Result = 1; goto finish; }
    Root = Abc_Lit2Var( Gia_ManAppendCo(pFree->pFrames, Bad) );
    Vec_IntPush( pFree->vRoots, Root );
    clk = Abc_Clock();
    Status = Bmc3G_AddCnf( pFree );
    Pars.timeCnf = Abc_Clock() - clk;
    if ( !Status || Bmc3G_Stop(pFree) ) goto finish;
    Lit = Vec_IntEntry( pFree->vVars, Root );
    assert( Lit > 0 );
    ccadical_assume( pFree->pSat, Lit );
    clk = Abc_Clock();
    p->nWindowQueries++;
    Status = ccadical_solve( pFree->pSat );
    Pars.timeSat = Abc_Clock() - clk;
    Result = Status == 20 && !ccadical_is_inconsistent(pFree->pSat);
finish:
    p->pPars->timeUnroll += Abc_Clock() - Start - Pars.timeCnf - Pars.timeSat;
    p->pPars->timeCnf += Pars.timeCnf;
    p->pPars->timeSat += Pars.timeSat;
    Bmc3G_StopManager( pFree );
    if ( Used + Pars.MemoryPeakMB > p->pPars->MemoryPeakMB )
        p->pPars->MemoryPeakMB = Used + Pars.MemoryPeakMB;
    if ( p->pPars->fVerbose )
        Abc_Print( 1, "BMC arbitrary-state window: depth=%d proved=%d time=%.3f sec.\n",
            Depth, Result, (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC );
    return Result;
}

/**Function*************************************************************

  Synopsis    [Runs incremental GIA BMC using one CaDiCaL instance.]

  Description [Returns 0 with a verified counterexample, 1 for a complete
  safety proof, -1 for undecided, and -2 for unsupported input. Completing
  a finite frame limit is not a proof. Complete exploration through the
  finite-state bound or closure of a ternary cycle establishes safety. Optional
  property-cone isomorphism preserves the depths of all reachable failures.]

  SideEffects [Replaces pGia->pCexSeq and updates the caller's statistics.]

  SeeAlso     []

***********************************************************************/
int Bmc_GiaPerformWindow( Gia_Man_t * pGia, Bmc_GiaPar_t * pPars, int nGroup )
{
    Bmc3G_Man_t * p;
    Gia_Obj_t * pObj;
    Abc_Cex_t * pCex = NULL;
    abctime clk, Start;
    int Frame, i, Lit, Root, Status, Result = -1, fTrivial = 1;
    int FirstGap = -1, LastGap = -1, Series = 0, Stride = 0, Targets = 0, Furthest = 0, Step, JumpLimit;
    int BaseLimit, Trigger, ConfLimit;
    ABC_INT64_T ForwardWork = 0, ProbeWork = 0, Credit;
    unsigned Before = 0;
    if ( !Bmc3G_CheckInput(pGia, pPars) ) return -2;
    if ( nGroup < 1 || nGroup > 256 || (nGroup > 1 && (pPars->pShared || pPars->fUseIso ||
         pPars->nFramesJump || Gia_ManPoNum(pGia) != 1)) ) return -2;
    if ( pPars->pShared && !pPars->pShared->pFuncFrames ) return -2;
    Trigger = BaseLimit = pPars->nConfLimit ? pPars->nConfLimit : 10000;
    pPars->nFramesDone = pPars->nFramesShared = pPars->nQueries = 0;
    pPars->fMemoryLimit = 0;
    pPars->iFrame = -1;
    pPars->timeUnroll = pPars->timeCnf = pPars->timeSat = 0;
    pPars->timeTeardown = pPars->timeSatOverrun = 0;
    pPars->MemoryPeakMB = 0;
    Abc_CexFreeP( &pGia->pCexSeq );
    p = Bmc3G_Start( pGia, pPars, 0 );
    if ( p->fStopped ) goto finish;
    JumpLimit = pPars->nFramesMax ? pPars->nFramesMax : INT_MAX - 1;
    if ( Gia_ManRegNum(p->pGia) < 30 )
        JumpLimit = Abc_MinInt( JumpLimit, 1 << Gia_ManRegNum(p->pGia) );
    Gia_ManForEachPo( p->pGia, pObj, i )
        fTrivial &= Gia_ObjFaninLit0p(p->pGia, pObj) == 0;
    if ( fTrivial ) { Result = 1; goto finish; }
    for ( Frame = 0; Frame < INT_MAX - 1 && (!pPars->nFramesMax || Frame < pPars->nFramesMax); Frame++ )
    {
        int fFrameTrivial = 1;
        if ( Bmc3G_Stop(p) ) break;
        clk = Abc_Clock();
        while ( Vec_PtrSize(p->vMaps) <= Frame )
        {
            if ( Bmc3G_Stop(p) || !Bmc3G_MapStart(p) ) goto finish;
        }
        if ( FirstGap < 0 && pPars->pShared && pPars->pShared->pFuncFrames(pPars->pShared->pData, 0) > Frame )
        {
            pPars->nFramesShared++;
            pPars->timeUnroll += Abc_Clock() - clk;
            goto frame_done;
        }
        if ( !pPars->nQueries ) Bmc3G_PropagateConstants(p, Frame);
        if ( nGroup == 1 && Frame == 16 && pPars->fTernaryPrefix && !pPars->nQueries && !pPars->pShared &&
             !p->fStopped && Gia_ManRegNum(p->pGia) )
        {
            int nRegs = Gia_ManRegNum(p->pGia);
            int Bound = nRegs < 30 ? 1 << nRegs : INT_MAX - 1;
            int Limit = pPars->nFramesMax ? Abc_MinInt(pPars->nFramesMax, Bound) : Bound;
            int fProved = Bmc3G_EventPrefix( p, Frame, Limit );
            if ( fProved || p->fStopped || pPars->nFramesDone >= Limit )
            {
                if ( fProved || (nRegs < 30 && pPars->nFramesDone == Bound) ) Result = 1;
                pPars->timeUnroll += Abc_Clock() - clk;
                break;
            }
        }
        if ( Frame < pPars->nFramesDone )
        {
            pPars->timeUnroll += Abc_Clock() - clk;
            goto frame_done;
        }
        if ( nGroup == 1 || pPars->nFramesDone == Frame ) Vec_IntClear( p->vRoots );
        Gia_ManForEachPo( p->pGia, pObj, i )
        {
            Lit = Bmc3G_Unroll( p, Gia_ObjFaninId0p(p->pGia, pObj), Frame );
            if ( Lit < 0 ) break;
            Lit ^= Gia_ObjFaninC0(pObj);
            fFrameTrivial &= Lit == 0;
            Root = Gia_ManAppendCo( p->pFrames, Lit );
            Vec_IntPush( p->vRoots, Abc_Lit2Var(Root) );
            if ( Lit == 1 )
            {
                pCex = Bmc3G_Cex( p, Frame, i, 0 );
                if ( pCex ) Result = 0;
                break;
            }
        }
        pPars->timeUnroll += Abc_Clock() - clk;
        if ( pCex || i < Gia_ManPoNum(p->pGia) ) break;
        if ( nGroup > 1 )
        {
            if ( Vec_IntSize(p->vRoots) < nGroup && Frame + 1 != pPars->nFramesMax &&
                 !(Gia_ManRegNum(p->pGia) < 30 && Frame + 1 >= (1 << Gia_ManRegNum(p->pGia))) )
                continue;
            fFrameTrivial = 1;
            Vec_IntForEachEntry(p->vRoots, Root, i)
                if ( Gia_ObjFaninLit0p(p->pFrames, Gia_ManObj(p->pFrames, Root)) != 0 ) { fFrameTrivial = 0; break; }
        }
        clk = Abc_Clock();
        if ( !fFrameTrivial && !Bmc3G_AddCnf(p) )
        {
            pPars->timeCnf += Abc_Clock() - clk;
            break;
        }
        pPars->timeCnf += Abc_Clock() - clk;
        if ( nGroup > 1 )
        {
            if ( fFrameTrivial ) goto frame_done;
            if ( Bmc3G_Stop(p) ) break;
            // Disjoin the bad outputs of this window for one SAT query.
            // CaDiCaL removes the temporary constraint after the solve.
            clk = Abc_Clock();
            Vec_IntForEachEntry(p->vRoots, Root, i)
                if ( Gia_ObjFaninLit0p(p->pFrames, Gia_ManObj(p->pFrames, Root)) != 0 )
                    ccadical_constrain(p->pSat, Vec_IntEntry(p->vVars, Root));
            ccadical_constrain(p->pSat, 0);
            if ( pPars->nConfLimit ) ccadical_limit(p->pSat, "conflicts", pPars->nConfLimit);
            pPars->nQueries++;
            Status = ccadical_solve(p->pSat);
            pPars->timeSat += Abc_Clock() - clk;
            if ( Status == 20 && !ccadical_is_inconsistent(p->pSat) ) goto frame_done;
            if ( Status == 10 )
                Vec_IntForEachEntry(p->vRoots, Root, i)
                {
                    if ( Gia_ObjFaninLit0p(p->pFrames, Gia_ManObj(p->pFrames, Root)) == 0 ) continue;
                    Lit = Vec_IntEntry(p->vVars, Root);
                    if ( ccadical_val(p->pSat, Lit) <= 0 ) continue;
                    pCex = Bmc3G_Cex(p, pPars->nFramesDone + i, 0, 1);
                    if ( pCex ) Result = 0;
                    break;
                }
            break;
        }
        Vec_IntForEachEntry( p->vRoots, Root, i )
        {
            pObj = Gia_ManObj( p->pFrames, Root );
            if ( Gia_ObjFaninLit0p(p->pFrames, pObj) == 0 ) continue;
            if ( Bmc3G_Stop(p) ) break;
            Lit = Vec_IntEntry( p->vVars, Root );
            assert( Lit > 0 );
            clk = Abc_Clock();
            ConfLimit = pPars->nConfLimit;
            if ( pPars->nFramesJump )
            {
                Before = (unsigned)ccadical_conflicts( p->pSat );
                if ( FirstGap < 0 )
                    ConfLimit = pPars->nConfLimit ? pPars->nConfLimit : Trigger;
                else
                {
                    Credit = ForwardWork + 8 * (ABC_INT64_T)BaseLimit - ProbeWork;
                    if ( Credit <= 0 ) goto next_jump;
                    ConfLimit = 2 * Abc_MinInt( BaseLimit, INT_MAX / 2 );
                    if ( Credit < ConfLimit ) ConfLimit = (int)Credit;
                }
            }
            if ( ConfLimit ) ccadical_limit( p->pSat, "conflicts", ConfLimit );
            ccadical_assume( p->pSat, Lit );
            pPars->nQueries++;
            Status = ccadical_solve( p->pSat );
            if ( pPars->nFramesJump )
            {
                // The difference of the low words is exact for one conflict-limited call.
                unsigned Used = (unsigned)ccadical_conflicts( p->pSat ) - Before;
                if ( FirstGap < 0 ) ForwardWork += Used;
                else                ProbeWork += Used;
            }
            pPars->timeSat += Abc_Clock() - clk;
            if ( p->Deadline && Abc_Clock() > p->Deadline )
                pPars->timeSatOverrun += Abc_Clock() - p->Deadline;
            if ( Status == 20 )
            {
                if ( !ccadical_is_inconsistent(p->pSat) ) continue;
                Abc_Print( 1, "Warning: &bmc3 detected contradictory circuit clauses; returning undecided.\n" );
            }
            if ( Status == 10 )
            {
                pCex = Bmc3G_Cex( p, Frame, i, 1 );
                if ( pCex ) Result = 0;
            }
            if ( Status == 0 && pPars->nFramesJump && !Bmc3G_Stop(p) &&
                 (FirstGap >= 0 || !pPars->nConfLimit || Frame != LastGap) )
                goto next_jump;
            break;
        }
        if ( i < Vec_IntSize(p->vRoots) ) break;
        // A refuted probe says nothing about the unchecked intervening frames.
        if ( FirstGap >= 0 ) goto next_jump;
        if ( pPars->pShared ) pPars->pShared->pFuncFrames( pPars->pShared->pData, Frame + 1 );
frame_done:
        Bmc3G_RecordFrames( p, Frame, nGroup == 1 ? 1 : Vec_IntSize(p->vRoots) );
        if ( Frame == 5 && pPars->nFramesDone == 6 && pPars->fWindowProof && !pPars->nConfLimit &&
             !pPars->pShared && Gia_ManPoNum(pGia) > 1 && Gia_ManRegNum(pGia) && Gia_ManObjNum(pGia) < 240000 &&
             (!pPars->nFramesMax || pPars->nFramesMax > 6) && Bmc3G_WindowProof(p, 6) )
        {
            Result = 1;
            break;
        }
        if ( Gia_ManRegNum(p->pGia) < 30 && Frame + 1 >= (1 << Gia_ManRegNum(p->pGia)) )
        {
            Result = 1;
            break;
        }
        continue;
next_jump:
        if ( FirstGap < 0 )
        {
            FirstGap = LastGap = Frame;
            Stride = pPars->nFramesJump - ((Series & 1) && pPars->nFramesJump > 1);
            ++Series;
            Targets = 0;
            if ( pPars->fVerbose )
                Abc_Print( 1, "BMC probe series %d: gap=%d stride=%d trigger=%d\n",
                    Series, Frame, Stride, Trigger );
        }
        // Charge actual probe conflicts to forward search, with a fixed opening allowance.
        // A target limit also bounds sequences of trivially refuted probes.
        // Alternate series revisit the other parity near the deepest previous probe.
        Step = Stride;
        if ( !Targets && !(Series & 1) && Furthest > Frame + 1 )
            Step = Abc_MaxInt( Step, Furthest - Frame - 1 );
        if ( Targets < 16 && ProbeWork < ForwardWork + 8 * (ABC_INT64_T)BaseLimit &&
             Step < JumpLimit - Frame )
        {
            ++Targets;
            Frame += Step - 1;
            Furthest = Abc_MaxInt( Furthest, Frame + 1 );
            if ( pPars->fVerbose )
                Abc_Print( 1, "BMC witness probe: frame=%d safe=%d\n", Frame + 1, pPars->nFramesDone );
        }
        else
        {
            if ( !pPars->nConfLimit )
                Trigger = Trigger <= INT_MAX / 2 ? 2 * Trigger : INT_MAX;
            Frame = FirstGap - 1;
            FirstGap = -1;
        }
    }
finish:
    if ( pCex && p->pOriginal )
    {
        Abc_Cex_t * pFull = NULL;
        // Abc_CexDup adds the new register count before subtracting the old count.
        if ( (ABC_INT64_T)pCex->nBits + Gia_ManRegNum(pGia) <= INT_MAX - 32 )
        {
            pFull = Abc_CexDup( pCex, Gia_ManRegNum(pGia) );
            if ( p->vOriginalPos ) pFull->iPo = Vec_IntEntry( p->vOriginalPos, pCex->iPo );
            else if ( Gia_ManPoNum(p->pOriginal) == 1 ) pFull->iPo = 0;
            if ( !Gia_ManVerifyCex(p->pOriginal, pFull, 0) )
            {
                Abc_Print( 1, "Warning: &bmc3 rejected a counterexample on the original graph.\n" );
                Abc_CexFreeP( &pFull );
            }
        }
        Abc_CexFree( pCex );
        pCex = pFull;
        Result = pCex ? 0 : -1;
    }
    pPars->nQueries += p->nWindowQueries;
    pPars->iFrame = pCex ? pCex->iFrame : pPars->nFramesDone - 1;
    pGia->pCexSeq = pCex;
    Start = p->Start;
    clk = Abc_Clock();
    Bmc3G_StopManager( p );
    pPars->timeTeardown = Abc_Clock() - clk;
    if ( pPars->fVerbose && pPars->pShared )
        Abc_Print( 1, "BMC shared prefix skipped %d frame queries.\n", pPars->nFramesShared );
    if ( pPars->fVerbose )
        Abc_Print( 1, "Bmc3: completed=%d queries=%d unroll=%.3f cnf=%.3f sat=%.3f sec\n",
            pPars->nFramesDone, pPars->nQueries, (double)pPars->timeUnroll / CLOCKS_PER_SEC,
            (double)pPars->timeCnf / CLOCKS_PER_SEC, (double)pPars->timeSat / CLOCKS_PER_SEC );
    if ( pPars->fVerbose )
        Abc_Print( 1, "Bmc3: teardown=%.3f sat-overrun=%.3f sec memory-estimate=%.1f MiB\n",
            (double)pPars->timeTeardown / CLOCKS_PER_SEC, (double)pPars->timeSatOverrun / CLOCKS_PER_SEC,
            pPars->MemoryPeakMB );
    if ( !pPars->fSilent )
    {
        if ( pPars->fMemoryLimit ) Abc_Print( 1, "&bmc3 reached its memory or object budget.\n" );
        Abc_Print( 1, "Problem \"%s\" is %s", pGia->pName ? pGia->pName : "network",
            Result == 0 ? "SATISFIABLE" : Result == 1 ? "UNSATISFIABLE" : "UNDECIDED" );
        if ( Result >= 0 ) Abc_Print( 1, " (solved by bmc3-cadical)" );
        Abc_Print( 1, ". Time = %.6f sec\n", (double)(Abc_Clock() - Start) / CLOCKS_PER_SEC );
    }
    return Result;
}

/**Function*************************************************************

  Synopsis    [Checks each output at every frame with incremental BMC.]

  Description []

***********************************************************************/
int Bmc_GiaPerform( Gia_Man_t * pGia, Bmc_GiaPar_t * pPars )
{
    return Bmc_GiaPerformWindow(pGia, pPars, 1);
}

/**Function*************************************************************

  Synopsis    [Encodes only the polarities required to make the requested outputs true.]

***********************************************************************/
static int Bmc3G_AddTargetCnf( Bmc3G_Man_t * p, int fPolarity )
{
    Gia_Man_t * pGia = p->pFrames;
    Gia_Obj_t * pObj;
    unsigned char * pNeed;
    int nObjs = Gia_ManObjNum(pGia), i, Id, Sign, Mask, Var, a, b, fReady = 0;
    if ( !fPolarity ) return Bmc3G_AddCnf(p);
    if ( Bmc3G_CheckMemory(p, 5.0*nObjs) ) return 0;
    pNeed = ABC_CALLOC(unsigned char, nObjs);
    Vec_IntFillExtra(p->vVars, nObjs, 0);
    Vec_IntForEachEntry(p->vRoots, Id, i) pNeed[Id] = 1;
    // Bit 0 requests the positive implication and bit 1 its converse.
    // Edges run from higher to lower IDs. Shared cones collect both
    // polarities before their fanins are visited.
    for ( i = nObjs-1; i > 0; --i )
    {
        if ( !(i & 4095) && Bmc3G_Stop(p) ) goto done;
        pObj = Gia_ManObj(pGia, i);
        if ( !(Mask = pNeed[i]) || Gia_ObjIsCi(pObj) ) continue;
        Sign = Gia_ObjFaninC0(pObj);
        pNeed[Gia_ObjFaninId0(pObj,i)] |= Sign ? ((Mask&1)<<1) | (Mask>>1) : Mask;
        if ( Gia_ObjIsCo(pObj) ) continue;
        Sign = Gia_ObjFaninC1(pObj);
        pNeed[Gia_ObjFaninId1(pObj,i)] |= Sign ? ((Mask&1)<<1) | (Mask>>1) : Mask;
    }
    for ( i = 1; i < nObjs; ++i )
    {
        if ( !(i & 4095) && (Bmc3G_Stop(p) || Bmc3G_CheckMemory(p, 5.0*nObjs)) ) goto done;
        if ( !(Mask = pNeed[i]) ) continue;
        pObj = Gia_ManObj(pGia, i);
        Var = ++p->nVars;
        Vec_IntWriteEntry(p->vVars, i, Var);
        if ( Gia_ObjIsCi(pObj) ) continue;
        a = Vec_IntEntry(p->vVars, Gia_ObjFaninId0(pObj,i));
        if ( Gia_ObjFaninC0(pObj) ) a = -a;
        if ( Mask & 1 )
        {
            ccadical_add(p->pSat, -Var); ccadical_add(p->pSat, a); ccadical_add(p->pSat, 0);
            p->nCnfLits += 2;
        }
        if ( Gia_ObjIsCo(pObj) ) { assert(Mask == 1); continue; }
        b = Vec_IntEntry(p->vVars, Gia_ObjFaninId1(pObj,i));
        if ( Gia_ObjFaninC1(pObj) ) b = -b;
        if ( Mask & 1 )
        {
            ccadical_add(p->pSat, -Var); ccadical_add(p->pSat, b); ccadical_add(p->pSat, 0);
            p->nCnfLits += 2;
        }
        if ( Mask & 2 )
        {
            ccadical_add(p->pSat, Var); ccadical_add(p->pSat, -a); ccadical_add(p->pSat, -b); ccadical_add(p->pSat, 0);
            p->nCnfLits += 3;
        }
    }
    fReady = 1;
done:
    ABC_FREE(pNeed);
    return fReady;
}

/**Function*************************************************************

  Synopsis    [Asserts a disjunction of bad outputs and reconstructs its failing frame.]

***********************************************************************/
static Abc_Cex_t * Bmc3G_SolveTargetWindow( Bmc3G_Man_t * p, Vec_Int_t * vFrames, int fPolarity )
{
    int Root, Var, i;
    if ( !Vec_IntSize(vFrames) || !Bmc3G_AddTargetCnf(p, fPolarity) || Bmc3G_Stop(p) ) return NULL;
    // This solver is dedicated to a single disjunction. Making it a clause
    // lets the SAT preprocessor use the property throughout simplification.
    Vec_IntForEachEntry(p->vRoots, Root, i)
        ccadical_add(p->pSat, Vec_IntEntry(p->vVars, Root));
    ccadical_add(p->pSat, 0);
    if ( p->pPars->nConfLimit ) ccadical_limit(p->pSat, "conflicts", p->pPars->nConfLimit);
    p->pPars->nQueries++;
    if ( ccadical_solve(p->pSat) != 10 ) return NULL;
    Vec_IntForEachEntry(p->vRoots, Root, i)
    {
        Var = Vec_IntEntry(p->vVars, Root);
        if ( ccadical_val(p->pSat, Var) > 0 )
            return Bmc3G_Cex(p, Vec_IntEntry(vFrames, i), 0, 1);
    }
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Searches a single depth, its last live output, or a whole prefix.]

  Description [Window 0 selects the specified depth. Window 1 selects the
  latest structurally possible failure up to that depth. Window 2 checks a
  single SAT disjunction over all structurally possible failures.]

***********************************************************************/
int Bmc_GiaFindTarget( Gia_Man_t * pGia, Bmc_GiaPar_t * pPars, int Frame, int nTerms, int Window, int fPolarity )
{
    Bmc3G_Man_t * p;
    Gia_Obj_t * pObj;
    Vec_Int_t * vTerms, * vFrames;
    Abc_Cex_t * pCex = NULL;
    int i, k, Best, Lit, Root, Status, Next = 1, Chosen = -1, Target = 0, Result = -1;
    if ( !Bmc3G_CheckInput(pGia,pPars) || Gia_ManPoNum(pGia) != 1 ||
         pPars->pShared || Frame < 0 || Frame > 256 || nTerms < 1 || nTerms > 64 || Window < 0 || Window > 2 ) return -1;
    Abc_CexFreeP(&pGia->pCexSeq);
    pPars->nQueries = pPars->nFramesDone = 0;
    pPars->iFrame = -1;
    p = Bmc3G_Start(pGia, pPars, 1);
    vTerms = Vec_IntAlloc(nTerms);
    vFrames = Vec_IntAlloc(Window == 2 ? Frame+1 : 0);
    for ( i = 0; i <= Frame; ++i )
    {
        if ( Bmc3G_Stop(p) || !Bmc3G_MapStart(p) ) goto done;
        Bmc3G_PropagateConstants(p, i);
        if ( !Window && i != Frame ) continue;
        if ( Bmc3G_Stop(p) ) goto done;
        pObj = Gia_ManPo(p->pGia, 0);
        Lit = Bmc3G_Unroll(p, Gia_ObjFaninId0p(p->pGia,pObj), i);
        if ( Lit < 0 ) goto done;
        Lit ^= Gia_ObjFaninC0(pObj);
        if ( !Lit ) continue;
        if ( Lit == 1 ) { pCex = Bmc3G_Cex(p, i, 0, 0); goto done; }
        Chosen = i;
        Target = Lit;
        if ( Window == 2 )
        {
            Vec_IntPush(vFrames, i);
            Root = Gia_ManAppendCo(p->pFrames, Lit);
            Vec_IntPush(p->vRoots, Abc_Lit2Var(Root));
        }
    }
    if ( Chosen < 0 || Bmc3G_Stop(p) ) goto done;
    if ( Window == 2 )
    {
        pCex = Bmc3G_SolveTargetWindow(p, vFrames, fPolarity);
        goto done;
    }
    Vec_IntPush(vTerms, Target);
    while ( Vec_IntSize(vTerms) < nTerms )
    {
        Best = -1;
        Vec_IntForEachEntry( vTerms, Lit, k )
            if ( !Abc_LitIsCompl(Lit) && Gia_ObjIsAnd(Gia_ManObj(p->pFrames, Abc_Lit2Var(Lit))) &&
                 (Best < 0 || Lit > Vec_IntEntry(vTerms, Best)) ) Best = k;
        if ( Best < 0 ) break;
        pObj = Gia_ManObj(p->pFrames, Abc_Lit2Var(Vec_IntEntry(vTerms, Best)));
        Vec_IntWriteEntry(vTerms, Best, Gia_ObjFaninLit0p(p->pFrames,pObj));
        Vec_IntPush(vTerms, Gia_ObjFaninLit1p(p->pFrames,pObj));
    }
    Vec_IntUniqify(vTerms);
    Vec_IntForEachEntry( vTerms, Lit, i )
    {
        Root = Gia_ManAppendCo(p->pFrames, Lit);
        Vec_IntPush(p->vRoots, Abc_Lit2Var(Root));
    }
    if ( !Bmc3G_AddTargetCnf(p, fPolarity) ) goto done;
    Vec_IntForEachEntry( p->vRoots, Root, i )
    {
        if ( Bmc3G_Stop(p) ) goto done;
        Lit = Vec_IntEntry(p->vVars, Root);
        assert(Lit > 0);
        ccadical_add(p->pSat, Lit); ccadical_add(p->pSat, 0);
        if ( i+1 < Vec_IntSize(p->vRoots) && i+1 != Next ) continue;
        Next *= 2;
        if ( i+1 < Vec_IntSize(p->vRoots) )
            ccadical_limit(p->pSat, "conflicts", pPars->nConfLimit ? Abc_MinInt(96, pPars->nConfLimit) : 96);
        else if ( pPars->nConfLimit ) ccadical_limit(p->pSat, "conflicts", pPars->nConfLimit);
        pPars->nQueries++;
        Status = ccadical_solve(p->pSat);
        if ( Status == 20 ) break;
        if ( Status == 10 && i+1 == Vec_IntSize(p->vRoots) ) pCex = Bmc3G_Cex(p, Chosen, 0, 1);
    }
done:
    if ( pCex )
    {
        pGia->pCexSeq = pCex;
        pPars->iFrame = pCex->iFrame;
        Result = 0;
    }
    if ( pPars->fVerbose )
        Abc_Print(1, "Bounded target: depth %d, selected frame %d, %d terms, %d window outputs, %d SAT queries, %d SAT variables, memory limit %d, result %d.\n",
            Frame, pCex ? pCex->iFrame : Chosen, Vec_IntSize(vTerms), Vec_IntSize(vFrames), pPars->nQueries, p->nVars, pPars->fMemoryLimit, Result);
    Vec_IntFree(vFrames);
    Vec_IntFree(vTerms);
    Bmc3G_StopManager(p);
    return Result;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
