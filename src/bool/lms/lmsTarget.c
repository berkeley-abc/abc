/**CFile****************************************************************

  FileName    [lmsTarget.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [LMS target-delay optimization.]

  Synopsis    [Experimental target-delay selection over direct GIA cuts.]

  Author      [Alan Mishchenko]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 6, 2026.]

  Revision    [$Id: lmsTarget.c,v 1.00 2026/10/06 00:00:00 alanmi Exp $]

***********************************************************************/

#include "lms.h"
#include "aig/gia/gia.h"
#include <limits.h>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Lmt_Cut_t_ Lmt_Cut_t;
struct Lmt_Cut_t_
{
    int Next, Root, Po, Area, Pos;
    const int * Leaves;
    const unsigned char * Depths;
    unsigned char nLeaves, Compl, ArrDelta;
};
typedef struct Lmt_Bind_t_ Lmt_Bind_t;
struct Lmt_Bind_t_
{
    int Next, Root, First, Leaves[6];
    const int * pPos;
    unsigned char nLeaves, Compl;
};
typedef struct Lmt_Profile_t_ Lmt_Profile_t;
struct Lmt_Profile_t_ { unsigned char Area, Depths[6]; };
typedef struct Lmt_Extra_t_ Lmt_Extra_t;
struct Lmt_Extra_t_ { int Bind, Po, Next, Repr; };
typedef struct Lmt_Alt_t_ Lmt_Alt_t;
struct Lmt_Alt_t_ { int Group, Repr, Po; };
typedef struct Lmt_Rank_t_ Lmt_Rank_t;
struct Lmt_Rank_t_ { int Choice, Cost, Level; };
typedef struct Lmt_Man_t_ Lmt_Man_t;
struct Lmt_Man_t_
{
    Gia_Man_t * pGia;
    Lmt_Bind_t * pBinds;
    Lmt_Profile_t * pProfiles;
    Lmt_Extra_t * pExtras;
    int * pOwners;
    unsigned char * pCutArrival; // lower bounds relative to the root's pMinArr
    int nBinds, nBindCap, nBaseCuts, nExtraCap, nFirstCuts;
    int nCuts, nCap, fFailed, Target, Exact;
    int fLazy, Depth, fDenseFallback;
    size_t nVisited, nStates, nHash, nAlternatives;
    int * pHash;
    unsigned nDuplicates;
    size_t * pOffsets;
    int * pHeads, * pChoice, * pRequired, * pSelected, * pRefs;
    int * pMinArr, * pConverge, * pDpOrder, * pDpStart, * pCoRequired;
    float * pCost, * pWeights, * pBound, * pNodeBound;
    Vec_Int_t * vPrograms, * vProgramOffsets, * vLabels, * vRefStack, * vTiming;
};

typedef struct Lmt_Union_t_ Lmt_Union_t;
struct Lmt_Union_t_
{
    Lmt_Man_t * p;
    Gia_Man_t * pGraph;
    Vec_Int_t * vRefs, * vLevels, * vSeen, * vStack, * vReq, * vLive;
    Vec_Int_t * vDirty, * vSaved, * vRefresh, * vExpand, * vGroupLevels;
    Vec_Int_t * vProbeMark, * vVirt, * vVirtMark, * vProbeStack;
    Vec_Wec_t * vFanouts;
    int * pLits, * pMarks, * pChanged, * pFresh;
    int Area, nRebases, nChanges, Stamp, RebaseAt, fReqDirty, DirtyRoot, ProbeStamp;
    double nCandidates, nTrials, nTouched, nLate, nNonnegative, nProfiles, nCurrent;
};

#ifndef LMS_TARGET_UNION_LIMIT
#define LMS_TARGET_UNION_LIMIT (2*1024*1024)
#endif

// Report large allocations independently of the optional deadline budget.
// Candidate storage has no fixed memory cap.
#define LMS_TARGET_MEMORY_NOTE ((size_t)256*1024*1024)

extern int Abc_RecTargetCost3( word, int, const int *, int *, Lms_CutMatch_t * );
extern int Abc_RecTargetCollect3( void *, int, int, const int *, word, const Lms_CutMatch_t * );
extern void Abc_RecTargetRecipe3( int, Vec_Int_t * );
extern int Abc_RecTargetReady3( void );
extern void Abc_RecTargetCache3( int );
extern int Abc_RecTargetNext3( int );
extern int Abc_RecTargetCount3( int );
extern int Abc_RecTargetData3( const unsigned char **, const word ** );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Add a unit-delay path without overflowing the time sentinel.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Lmt_AddDelay( int Arrival, int Delay )
{
    return Abc_MinInt(Arrival, ABC_INFINITY-Delay) + Delay;
}

/**Function*************************************************************

  Synopsis    [Read an output's effective deadline.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Lmt_CoRequired( Lmt_Man_t * p, int iCo )
{
    return p->pCoRequired ? p->pCoRequired[iCo] : p->Target;
}

/**Function*************************************************************

  Synopsis    [Measure arrivals using reusable manager-owned scratch storage.]

  Description [CI order is preserved by reconstruction. The optional input
  arrivals belong to the original graph; internal graph IDs may differ.]

  SideEffects [Overwrites the timing scratch vector.]

  SeeAlso     []

***********************************************************************/
static void Lmt_TimingLevels( Lmt_Man_t * p, Gia_Man_t * pGia )
{
    Vec_Int_t * vCiArrs = p->pGia->vCiArrs;
    Gia_Obj_t * pObj;
    int Id, * pLevels;
    if ( !p->vTiming ) p->vTiming = Vec_IntAlloc(0);
    Vec_IntGrowResize(p->vTiming, Gia_ManObjNum(pGia));
    pLevels = Vec_IntArray(p->vTiming);
    pLevels[0] = 0;
    Gia_ManForEachObj1(pGia, pObj, Id)
    {
        if ( Gia_ObjIsCi(pObj) )
            pLevels[Id] = vCiArrs ? Vec_IntEntry(vCiArrs, Gia_ObjCioId(pObj)) : 0;
        else if ( Gia_ObjIsAnd(pObj) )
            pLevels[Id] = Lmt_AddDelay(Abc_MaxInt(
                pLevels[Gia_ObjFaninId0p(pGia, pObj)], pLevels[Gia_ObjFaninId1p(pGia, pObj)]), 1);
        else
        {
            assert(Gia_ObjIsCo(pObj));
            pLevels[Id] = pLevels[Gia_ObjFaninId0p(pGia, pObj)];
        }
    }
}

/**Function*************************************************************

  Synopsis    [Save measured output arrivals for the result's timing metadata.]

  Description []

  SideEffects [Overwrites the timing scratch vector.]

  SeeAlso     []

***********************************************************************/
static Vec_Int_t * Lmt_CoArrivals( Lmt_Man_t * p, Gia_Man_t * pGia )
{
    Vec_Int_t * vArrivals = Vec_IntAlloc(Gia_ManCoNum(pGia));
    Gia_Obj_t * pObj;
    int i;
    Lmt_TimingLevels(p, pGia);
    Gia_ManForEachCo(pGia, pObj, i)
        Vec_IntPush(vArrivals, Vec_IntEntry(p->vTiming, Gia_ObjId(pGia, pObj)));
    return vArrivals;
}

/**Function*************************************************************

  Synopsis    [Validate physical output arrivals against every deadline.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmt_CheckTiming( Lmt_Man_t * p, Gia_Man_t * pGia )
{
    Gia_Obj_t * pObj;
    int i;
    if ( !p->pGia->vCiArrs && !p->pGia->vCoReqs )
        return Gia_ManLevelNum(pGia) <= p->Target;
    Lmt_TimingLevels(p, pGia);
    Gia_ManForEachCo(pGia, pObj, i)
        if ( Vec_IntEntry(p->vTiming, Gia_ObjId(pGia, pObj)) > Lmt_CoRequired(p, i) ) return 0;
    return 1;
}

// Cache the topology once per used library PO. Bindings remain per candidate;
// no repeated DFS of the library is needed when hashing the same structure.
/**Function*************************************************************

  Synopsis    [Hash a direct gate or library recipe with the given leaf literals.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmt_BuildMacro( Lmt_Man_t * p, Gia_Man_t * pNew, int Po, int n, int * pLeaves, int Compl )
{
    int i, Offset, Count, * pCode, * pLabels;
    if ( Po == -2 )
    {
        assert(n == 2);
        return Abc_LitNotCond(Gia_ManHashAnd(pNew, pLeaves[0], pLeaves[1]), Compl);
    }
    if ( Po < 0 ) return Abc_LitNotCond(n ? pLeaves[0] : 0, Compl);
    Vec_IntFillExtra(p->vProgramOffsets, Po+1, -1);
    Offset = Vec_IntEntry(p->vProgramOffsets, Po);
    if ( Offset < 0 )
    {
        Offset = Vec_IntSize(p->vPrograms);
        Abc_RecTargetRecipe3(Po, p->vPrograms);
        Vec_IntWriteEntry(p->vProgramOffsets, Po, Offset);
    }
    pCode = Vec_IntArray(p->vPrograms)+Offset;
    Count = *pCode++;
    Vec_IntFill(p->vLabels, 6+Count, 0);
    pLabels = Vec_IntArray(p->vLabels);
    for ( i = 0; i < n; ++i ) pLabels[i] = pLeaves[i];
    for ( i = 0; i < Count; ++i )
        pLabels[6+i] = Gia_ManHashAnd(pNew,
            Abc_LitNotCond(pLabels[Abc_Lit2Var(pCode[2*i])], Abc_LitIsCompl(pCode[2*i])),
            Abc_LitNotCond(pLabels[Abc_Lit2Var(pCode[2*i+1])], Abc_LitIsCompl(pCode[2*i+1])));
    return Abc_LitNotCond(pLabels[Abc_Lit2Var(pCode[2*Count])], Abc_LitIsCompl(pCode[2*Count]) ^ Compl);
}

/**Function*************************************************************

  Synopsis    [Hash the root, leaves, and phase of a canonical binding.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned Lmt_CutHash( const Lmt_Bind_t * pCut )
{
    unsigned h = (unsigned)pCut->Root * 12582917u;
    int k;
    h ^= 2u*pCut->nLeaves + pCut->Compl;
    for ( k = 0; k < pCut->nLeaves; ++k ) h = 33*h ^ (unsigned)pCut->Leaves[k];
    h = (h ^ (h >> 16)) * 0x7feb352du;
    return h ^ (h >> 15);
}
/**Function*************************************************************

  Synopsis    [Compare canonical bindings without inspecting padding.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmt_CutEqual( const Lmt_Bind_t * pA, const Lmt_Bind_t * pB )
{
    return pA->Root == pB->Root && pA->pPos == pB->pPos &&
        pA->nLeaves == pB->nLeaves && pA->Compl == pB->Compl &&
        !memcmp(pA->Leaves, pB->Leaves, pA->nLeaves*sizeof(int));
}
/**Function*************************************************************

  Synopsis    [Grow and rebuild the canonical binding hash table.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmt_HashGrow( Lmt_Man_t * p )
{
    size_t nHash;
    int i, * pHash;
    if ( p->nHash > (size_t)-1 / sizeof(int) / 2 )
    {
        Abc_Print(-1, "LMS target: candidate hash size exceeds addressable storage.\n");
        p->fFailed = 1;
        return 0;
    }
    nHash = p->nHash ? 2*p->nHash : 8192;
    pHash = ABC_CALLOC(int, nHash);
    if ( !pHash )
    {
        Abc_Print(-1, "LMS target: cannot allocate %.2f MiB for the candidate hash.\n", (double)nHash*sizeof(int)/(1024*1024));
        p->fFailed = 1;
        return 0;
    }
    ABC_FREE(p->pHash);
    p->nHash = nHash;
    p->pHash = pHash;
    for ( i = 0; i < p->nBinds; ++i )
    {
        size_t Slot = Lmt_CutHash(p->pBinds+i) & (p->nHash-1);
        while ( p->pHash[Slot] ) Slot = (Slot+1) & (p->nHash-1);
        p->pHash[Slot] = i+1;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Grow candidate storage with allocation and overflow checks.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void * Lmt_Reserve( Lmt_Man_t * p, void * pOld, int * pCap, size_t Needed, size_t Size )
{
    void * pNew;
    int Cap = *pCap ? *pCap : 4096;
    if ( Needed <= (size_t)*pCap ) return pOld;
    if ( Needed > INT_MAX || Needed > (size_t)-1 / Size )
    {
        Abc_Print(-1, "LMS target: candidate count exceeds addressable storage.\n");
        p->fFailed = 1;
        return pOld;
    }
    while ( (size_t)Cap < Needed ) Cap = Cap > INT_MAX/2 ? INT_MAX : 2*Cap;
    if ( (size_t)Cap > (size_t)-1 / Size ) Cap = (int)Needed;
    pNew = realloc(pOld, (size_t)Cap*Size);
    if ( !pNew )
    {
        Abc_Print(-1, "LMS target: cannot allocate %.2f MiB for candidates.\n", (double)Cap*Size/(1024*1024));
        p->fFailed = 1;
        return pOld;
    }
    *pCap = Cap;
    if ( (size_t)Cap*Size > LMS_TARGET_MEMORY_NOTE )
        Abc_Print(0, "LMS target: candidate storage grows to %.2f MiB; continuing.\n", (double)Cap*Size/(1024*1024));
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Save one canonical leaf binding and its shared library profiles.]

  Description [Grows candidate storage as needed and reports large allocations.
  Allocation or index overflow refuses the transaction without pruning cuts.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Lms_TargetCut( void * pData, int Root, int nLeaves, const int * pLeaves,
    int Compl, const int * pPos, int nPos )
{
    Lmt_Man_t * p = (Lmt_Man_t *)pData;
    Lmt_Bind_t Cut, * pCut;
    size_t Slot;
    int k;
    if ( p->fFailed ) return;
    memset(&Cut, 0, sizeof(Cut));
    Cut.Root = Root;
    Cut.pPos = pPos;
    Cut.nLeaves = (unsigned char)nLeaves;
    Cut.Compl = (unsigned char)Compl;
    for ( k = 0; k < nLeaves; ++k )
    {
        assert(Abc_Lit2Var(pLeaves[k]) < Root);
        Cut.Leaves[k] = pLeaves[k];
    }
    if ( (!p->nHash || (size_t)p->nBinds >= p->nHash/2) && !Lmt_HashGrow(p) ) return;
    Slot = Lmt_CutHash(&Cut) & (p->nHash-1);
    while ( p->pHash[Slot] )
    {
        pCut = p->pBinds + p->pHash[Slot]-1;
        if ( Lmt_CutEqual(pCut, &Cut) )
        { p->nDuplicates += nPos; return; }
        Slot = (Slot+1) & (p->nHash-1);
    }
    p->pBinds = (Lmt_Bind_t *)Lmt_Reserve(p, p->pBinds, &p->nBindCap, (size_t)p->nBinds+1, sizeof(Lmt_Bind_t));
    if ( p->fFailed ) return;
    p->pOwners = (int *)Lmt_Reserve(p, p->pOwners, &p->nCap, (size_t)p->nCuts+nPos, sizeof(int));
    if ( p->fFailed ) return;
    pCut = p->pBinds + p->nBinds;
    *pCut = Cut;
    pCut->First = p->nCuts;
    pCut->Next = p->pHeads[Root];
    p->pHash[Slot] = p->nBinds+1;
    for ( k = 0; k < nPos; ++k )
    {
        p->pOwners[p->nCuts++] = p->nBinds;
        p->nAlternatives += Abc_RecTargetCount3(pPos ? pPos[k] : -1);
    }
    p->pHeads[Root] = p->nCuts-1;
    ++p->nBinds;
}

/**Function*************************************************************

  Synopsis    [Return the next base or expanded candidate at a root.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Lmt_Next( Lmt_Man_t * p, int c )
{
    Lmt_Bind_t * b;
    if ( c >= p->nBaseCuts ) return p->pExtras[c-p->nBaseCuts].Next;
    b = p->pBinds+p->pOwners[c];
    return c > b->First ? c-1 : b->Next;
}
/**Function*************************************************************

  Synopsis    [Return the canonical binding of a candidate.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Lmt_Owner( Lmt_Man_t * p, int c )
{
    return c < p->nBaseCuts ? p->pOwners[c] : p->pExtras[c-p->nBaseCuts].Bind;
}
/**Function*************************************************************

  Synopsis    [Return the library output of a candidate.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Lmt_Po( Lmt_Man_t * p, int c )
{
    Lmt_Bind_t * b;
    if ( c >= p->nBaseCuts ) return p->pExtras[c-p->nBaseCuts].Po;
    b = p->pBinds+p->pOwners[c];
    return b->pPos ? b->pPos[c-b->First] : -1;
}
/**Function*************************************************************

  Synopsis    [Compare choices by canonical binding and library output.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Lmt_SameChoice( Lmt_Man_t * p, int a, int b )
{
    return a == b || (a >= 0 && b >= 0 &&
        Lmt_Owner(p, a) == Lmt_Owner(p, b) && Lmt_Po(p, a) == Lmt_Po(p, b));
}
/**Function*************************************************************

  Synopsis    [Read a candidate from its shared binding and profile.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Lmt_GetCut( Lmt_Man_t * p, int c, Lmt_Cut_t * pCut )
{
    Lmt_Bind_t * b = p->pBinds+Lmt_Owner(p, c);
    int Po = Lmt_Po(p, c);
    pCut->Next = Lmt_Next(p, c);
    pCut->Root = b->Root;
    pCut->Po = Po;
    pCut->Area = p->pProfiles[Po+2].Area;
    pCut->Depths = p->pProfiles[Po+2].Depths;
    pCut->Leaves = b->Leaves;
    pCut->nLeaves = b->nLeaves;
    pCut->Compl = b->Compl;
    // The original gate wins ties, then the first bank, then new cuts.
    // Each collection keeps its original reverse order within that tier.
    pCut->Pos = c < p->nFirstCuts ? p->nFirstCuts-c : p->nBaseCuts-(c-p->nFirstCuts);
    pCut->ArrDelta = c < p->nBaseCuts ? p->pCutArrival[c] : 0;
}

/**Function*************************************************************

  Synopsis    [Unpack library areas and pin depths once per optimization.]

  Description [PO -2 is a direct AND, PO -1 is a constant or wire, and
  nonnegative POs denote library structures. Their profiles start at index 2.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmt_Profiles( Lmt_Man_t * p )
{
    const unsigned char * pAreas;
    const word * pDelays;
    int i, k, n = Abc_RecTargetData3(&pAreas, &pDelays);
    p->pProfiles = ABC_CALLOC(Lmt_Profile_t, (size_t)n+2);
    if ( !p->pProfiles )
    { Abc_Print(-1, "LMS target: cannot allocate library profiles.\n"); return 0; }
    p->pProfiles[0].Area = 1;
    p->pProfiles[0].Depths[0] = p->pProfiles[0].Depths[1] = 1;
    for ( i = 0; i < n; ++i )
    {
        p->pProfiles[i+2].Area = pAreas[i];
        for ( k = 0; k < 6; ++k ) p->pProfiles[i+2].Depths[k] = (unsigned char)((pDelays[i] >> (4*k)) & 15);
    }
    return 1;
}
/**Function*************************************************************

  Synopsis    [Estimate allocated candidate-table storage.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static double Lmt_BankBytes( Lmt_Man_t * p )
{
    return (double)p->nBindCap*sizeof(Lmt_Bind_t) + (double)p->nCap*sizeof(int) +
        (double)p->nBaseCuts*(sizeof(unsigned char)+sizeof(int)+sizeof(float)) +
        (double)p->nHash*sizeof(int) + (double)p->nExtraCap*sizeof(Lmt_Extra_t);
}

// Deadlines below the earliest arrival are infeasible and need no entries.
// Keep one sentinel slot when even the target is below the earliest arrival.
/**Function*************************************************************

  Synopsis    [Return the first stored deadline, including infeasible sentinels.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Lmt_FirstDeadline( Lmt_Man_t * p, int Id )
{
    return Abc_MinInt(p->pMinArr[Id], p->Target);
}
/**Function*************************************************************

  Synopsis    [Return the convergence deadline, capped by the target.]

  Description [Later deadlines have identical costs and choices for any
  fixed sharing weights, so their queries reuse this final slot exactly.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Lmt_LastDeadline( Lmt_Man_t * p, int Id )
{
    return Abc_MinInt(p->pConverge[Id], p->Target);
}
/**Function*************************************************************

  Synopsis    [Count deadline slots for a uniform slack window.]

  Description [Structural reference counts are still available here. An AND
  with no ordinary consumer cannot be a selected leaf; retain just its
  sentinel slot, even if it supplies sibling cuts to a representative.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static size_t Lmt_DeadlineSlots( Lmt_Man_t * p, int Slack )
{
    Gia_Obj_t * pObj;
    size_t Slots = 0, MaxSlots = (size_t)-1/(sizeof(float)+sizeof(int));
    int Id;
    Gia_ManForEachObj(p->pGia, pObj, Id)
    {
        size_t Count = Gia_ObjIsAnd(pObj) && p->pRefs[Id] ? (size_t)Abc_MinInt(Slack, Lmt_LastDeadline(p, Id)-Lmt_FirstDeadline(p, Id))+1 : 1;
        if ( Count > MaxSlots-Slots ) return MaxSlots+1;
        Slots += Count;
    }
    return Slots;
}

// Above the requested budget, retain the largest uniform slack window above
// each node's earliest arrival. A clamped query reuses a tighter solution,
// which remains feasible for the actual deadline. Even a zero-slack window
// retains the earliest feasible cover. This can restrict area optimization,
// so leave ordinary tables complete and allow -M 0 to disable the budget.
/**Function*************************************************************

  Synopsis    [Lay out feasible deadlines within the requested memory budget.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmt_DeadlineLayout( Lmt_Man_t * p, int Memory )
{
    Gia_Obj_t * pObj;
    size_t BytesPerSlot = sizeof(float)+sizeof(int), Units = 1024*1024/BytesPerSlot;
    size_t MaxSlots = (size_t)-1/BytesPerSlot, Budget = MaxSlots;
    size_t Full = Lmt_DeadlineSlots(p, p->Target), Slots = 0;
    int Id, Low = 0, High = p->Target, Slack = p->Target;
    if ( Memory && (size_t)Memory <= MaxSlots/Units ) Budget = (size_t)Memory*Units;
    if ( Memory && Full > Budget )
    {
        while ( Low < High )
        {
            int Mid = Low+(High-Low+1)/2;
            if ( Lmt_DeadlineSlots(p, Mid) <= Budget ) Low = Mid;
            else High = Mid-1;
        }
        Slack = Low;
    }
    if ( Lmt_DeadlineSlots(p, Slack) > MaxSlots )
    { Abc_Print(-1, "LMS target: deadline table size exceeds addressable storage.\n"); return 0; }
    Gia_ManForEachObj(p->pGia, pObj, Id)
    {
        p->pOffsets[Id] = Slots;
        Slots += Gia_ObjIsAnd(pObj) && p->pRefs[Id] ? (size_t)Abc_MinInt(Slack, Lmt_LastDeadline(p, Id)-Lmt_FirstDeadline(p, Id))+1 : 1;
    }
    p->pOffsets[Gia_ManObjNum(p->pGia)] = Slots;
    p->nStates = Slots-(Gia_ManObjNum(p->pGia)-Gia_ManAndNum(p->pGia));
    if ( Slack < p->Target )
        Abc_Print(0, "LMS target: deadline table %.2f MiB; slack capped at %d levels by -M %d (full range %s%.2f MiB). Use -M 0 for all deadlines.\n",
            (double)Slots*BytesPerSlot/(1024*1024), Slack, Memory,
            Full > MaxSlots ? "at least " : "", (double)Full*BytesPerSlot/(1024*1024));
    else if ( Slots*BytesPerSlot > LMS_TARGET_MEMORY_NOTE )
        Abc_Print(0, "LMS target: deadline table uses %.2f MiB; continuing with all feasible deadlines.\n", (double)Slots*BytesPerSlot/(1024*1024));
    if ( Slots > Budget )
        Abc_Print(0, "LMS target: minimum deadline table exceeds -M %d; retaining one slot per object and continuing.\n", Memory);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Clamp a deadline query to its stored feasible window.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static size_t Lmt_Index( Lmt_Man_t * p, int Id, int Required )
{
    int Limit = (int)(p->pOffsets[Id+1]-p->pOffsets[Id]-1);
    int First = Lmt_FirstDeadline(p, Id);
    assert(Required >= First && First <= p->Target);
    return p->pOffsets[Id] + Abc_MinInt(Required-First, Limit);
}
static void Lmt_ComputeLazy( Lmt_Man_t * p, int Id, int Required );
/**Function*************************************************************

  Synopsis    [Read or lazily compute the area-flow cost at a deadline.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static float Lmt_Cost( Lmt_Man_t * p, int Id, int Required )
{
    size_t Slot;
    if ( Required < p->pMinArr[Id] ) return 1.0e30f; // includes Required < 0
    Slot = Lmt_Index(p, Id, Required);
    if ( p->fLazy && p->pChoice[Slot] == -2 ) Lmt_ComputeLazy(p, Id, Required);
    return p->pCost[Slot];
}

// The dense and demand-driven evaluators share the same recurrence, traversal
// order, strict tie-break, and float arithmetic. Store each fanout-discounted
// result once instead of repeating the division at every consumer.
// Candidates are scanned in ascending-area order; ties in cost are resolved
// by chain position with the original gate first, which is the same choice
// the chain-order scan makes. Candidates that cannot meet deadline d, or whose
// deadline-independent lower bound exceeds the best cost, are skipped.
/**Function*************************************************************

  Synopsis    [Select the least area-flow cost for one node and deadline.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Lmt_ComputeSlot( Lmt_Man_t * p, int Id, int d )
{
    Gia_Obj_t * pObj = Gia_ManObj(p->pGia, Id);
    int i, k, Choice = -1, BestPos = -1, fStartedLazy = p->fLazy;
    size_t Slot = p->pOffsets[Id] + d-Lmt_FirstDeadline(p, Id);
    float Best = 1 + Lmt_Cost(p, Gia_ObjFaninId0p(p->pGia, pObj), d-1)
                   + Lmt_Cost(p, Gia_ObjFaninId1p(p->pGia, pObj), d-1);
    if ( fStartedLazy && !p->fLazy ) return; // dense fallback filled this slot
    for ( i = p->pDpStart[Id]; i < p->pDpStart[Id+1]; ++i )
    {
        int c = p->pDpOrder[i];
        Lmt_Cut_t Cut, * pCut = &Cut;
        float Cost;
        Lmt_GetCut(p, c, pCut);
        Cost = (float)pCut->Area;
        if ( Cost > Best ) break;
        if ( d-p->pMinArr[Id] < pCut->ArrDelta || p->pBound[c] > Best ) continue;
        for ( k = 0; k < pCut->nLeaves && Cost <= Best; ++k )
        {
            Cost += Lmt_Cost(p, Abc_Lit2Var(pCut->Leaves[k]), d-pCut->Depths[k]);
            if ( fStartedLazy && !p->fLazy ) return;
        }
        if ( Cost < Best || (Cost == Best && pCut->Pos < BestPos) )
        { Best = Cost; Choice = c; BestPos = pCut->Pos; }
    }
#ifdef LMS_TARGET_CHECK_UNION
    // Dense-mode oracle retains the old chain scan and first-minimum rule.
    // It also checks lower-bound pruning independently of candidate sorting.
    if ( !p->fLazy )
    {
        int c, RefChoice = -1;
        float RefBest = 1 + Lmt_Cost(p, Gia_ObjFaninId0p(p->pGia, pObj), d-1)
                          + Lmt_Cost(p, Gia_ObjFaninId1p(p->pGia, pObj), d-1);
        for ( c = p->pHeads[Id]; c >= 0; c = Lmt_Next(p, c) )
        {
            Lmt_Cut_t Cut, * pCut = &Cut;
            float Cost;
            Lmt_GetCut(p, c, pCut);
            Cost = (float)pCut->Area;
            for ( k = 0; k < pCut->nLeaves && Cost < RefBest; ++k )
                Cost += Lmt_Cost(p, Abc_Lit2Var(pCut->Leaves[k]), d-pCut->Depths[k]);
            if ( Cost < RefBest ) { RefBest = Cost; RefChoice = c; }
        }
        assert((Best >= 1.0e29f && RefBest >= 1.0e29f) || (Best == RefBest && Choice == RefChoice));
    }
#endif
    // Never discount the infeasible sentinel into an apparently feasible cost.
    p->pCost[Slot] = Best >= 1.0e29f ? 1.0e30f : Best / p->pWeights[Id];
    p->pChoice[Slot] = Choice;
    ++p->nVisited;
}

/**Function*************************************************************

  Synopsis    [Compute area-flow choices indexed by output deadline.]

  Description [Compare the original gate and library alternatives at every
  available deadline, including slack. Negative choices denote original
  gates (-1). Library PO identities are never reselected during emission.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Lmt_ComputeDense( Lmt_Man_t * p )
{
    Gia_Obj_t * pObj;
    int Id;
    size_t d;
    p->fLazy = 0;
    Gia_ManForEachObj(p->pGia, pObj, Id)
    {
        size_t Limit = p->pOffsets[Id+1]-p->pOffsets[Id]-1;
        if ( !Gia_ObjIsAnd(pObj) )
        {
            p->pCost[p->pOffsets[Id]] = 0;
            continue;
        }
        for ( d = 0; d <= Limit; ++d ) Lmt_ComputeSlot(p, Id, Lmt_FirstDeadline(p, Id)+(int)d);
    }
}

/**Function*************************************************************

  Synopsis    [Evaluate a deadline on demand with bounded recursion.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Lmt_ComputeLazy( Lmt_Man_t * p, int Id, int Required )
{
    // Protect the C stack independently of the AIG depth and user deadline.
    // Suspended lazy callers return without overwriting the dense results.
    if ( p->Depth == 128 )
    {
        p->fDenseFallback = 1;
        p->nVisited = 0;
        Lmt_ComputeDense(p);
        return;
    }
    ++p->Depth;
    Lmt_ComputeSlot(p, Id, Lmt_FirstDeadline(p, Id)+(int)(Lmt_Index(p, Id, Required)-p->pOffsets[Id]));
    --p->Depth;
}

/**Function*************************************************************

  Synopsis    [Initialize lazy evaluation or compute the complete deadline table.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Lmt_Compute( Lmt_Man_t * p, int fLazy )
{
    Gia_Obj_t * pObj;
    int Id;
    size_t d;
    p->nVisited = 0;
    p->Depth = p->fDenseFallback = 0;
    p->fLazy = fLazy;
    if ( !fLazy ) { Lmt_ComputeDense(p); return; }
    Gia_ManForEachObj(p->pGia, pObj, Id)
        if ( Gia_ObjIsAnd(pObj) )
            for ( d = p->pOffsets[Id]; d < p->pOffsets[Id+1]; ++d ) p->pChoice[d] = -2;
        else
        { p->pChoice[p->pOffsets[Id]] = -1; p->pCost[p->pOffsets[Id]] = 0; }
}

// Earliest arrival and convergence of every node over the whole bank, and
// a fixed per-node candidate order by ascending area and chain position.
/**Function*************************************************************

  Synopsis    [Compute deadline bounds and stable area-ordered candidates.]

  Description [A node's cost and choice converge once every candidate's
  leaves have converged at their pin deadlines. Take the maximum over all
  candidates and the original gate. This bound is independent of sharing
  weights, so it applies in every round. Saturate sums to avoid overflow.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmt_Prepare( Lmt_Man_t * p )
{
    Gia_Obj_t * pObj;
    int Id, c, k, i, nObjs = Gia_ManObjNum(p->pGia);
    p->pMinArr = ABC_CALLOC(int, nObjs);
    p->pConverge = ABC_CALLOC(int, nObjs);
    p->pCutArrival = ABC_CALLOC(unsigned char, p->nCuts);
    p->pDpStart = ABC_CALLOC(int, nObjs+1);
    p->pDpOrder = ABC_ALLOC(int, p->nCuts);
    p->pBound = ABC_ALLOC(float, p->nCuts);
    p->pNodeBound = ABC_ALLOC(float, nObjs);
    if ( !p->pMinArr || !p->pConverge || !p->pDpStart || !p->pNodeBound ||
         (p->nCuts && (!p->pDpOrder || !p->pBound || !p->pCutArrival)) )
    { Abc_Print(-1, "LMS target: cannot allocate candidate ordering and bounds.\n"); return 0; }
    if ( p->pGia->vCiArrs )
        Gia_ManForEachCi(p->pGia, pObj, i)
            p->pMinArr[Gia_ObjId(p->pGia, pObj)] = p->pConverge[Gia_ObjId(p->pGia, pObj)] = Vec_IntEntry(p->pGia->vCiArrs, i);
    Gia_ManForEachObj(p->pGia, pObj, Id)
    {
        int Arr, Converge;
        if ( !Gia_ObjIsAnd(pObj) ) continue;
        Arr = Lmt_AddDelay(Abc_MaxInt(p->pMinArr[Gia_ObjFaninId0p(p->pGia, pObj)], p->pMinArr[Gia_ObjFaninId1p(p->pGia, pObj)]), 1);
        Converge = 1 + Abc_MinInt(INT_MAX-1, Abc_MaxInt(p->pConverge[Gia_ObjFaninId0p(p->pGia, pObj)], p->pConverge[Gia_ObjFaninId1p(p->pGia, pObj)]));
        for ( c = p->pHeads[Id]; c >= 0; c = Lmt_Next(p, c) )
        {
            Lmt_Cut_t Cut, * pCut = &Cut;
            int A = 0, C = 0;
            Lmt_GetCut(p, c, pCut);
            for ( k = 0; k < pCut->nLeaves; ++k )
            {
                int Leaf = Abc_Lit2Var(pCut->Leaves[k]), Depth = pCut->Depths[k];
                A = Abc_MaxInt(A, Lmt_AddDelay(p->pMinArr[Leaf], Depth));
                C = Abc_MaxInt(C, Abc_MinInt(p->pConverge[Leaf], INT_MAX-Depth) + Depth);
            }
            // Ordering is built below. Reuse its array for absolute arrivals
            // until the minimum across all bindings of this node is known.
            p->pDpOrder[c] = A;
            Arr = Abc_MinInt(Arr, A);
            Converge = Abc_MaxInt(Converge, C);
        }
        p->pMinArr[Id] = Arr;
        p->pConverge[Id] = Converge;
        assert(Arr <= Converge);
    }
    for ( c = 0; c < p->nCuts; ++c )
    {
        int Delta = p->pDpOrder[c] - p->pMinArr[p->pBinds[p->pOwners[c]].Root];
        assert(Delta >= 0);
        // A common CI offset no longer disables this cheap feasibility test.
        // Different bindings can still have arbitrarily different arrivals;
        // saturating their delta keeps a sound, possibly weaker lower bound.
        p->pCutArrival[c] = (unsigned char)Abc_MinInt(Delta, 255);
    }
    for ( Id = 0, i = 0; Id < nObjs; ++Id )
    {
        int Counts[256] = {0}, Next[256];
        p->pDpStart[Id] = i;
        if ( p->pHeads[Id] < 0 ) continue;
        for ( c = p->pHeads[Id]; c >= 0; c = Lmt_Next(p, c) )
        {
            ++Counts[p->pProfiles[Lmt_Po(p, c)+2].Area];
        }
        for ( k = 0; k < 256; ++k ) { Next[k] = i; i += Counts[k]; }
        // The chain already orders ties by position. Preserve this order.
        for ( c = p->pHeads[Id]; c >= 0; c = Lmt_Next(p, c) )
            p->pDpOrder[Next[p->pProfiles[Lmt_Po(p, c)+2].Area]++] = c;
    }
    p->pDpStart[nObjs] = i;
    assert(i == p->nCuts);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Release derived bank bounds before rebuilding or stopping.]

  Description []

  SideEffects []

  SeeAlso     [Lmt_Prepare]

***********************************************************************/
static void Lmt_FreePrepare( Lmt_Man_t * p )
{
    ABC_FREE(p->pMinArr); ABC_FREE(p->pConverge); ABC_FREE(p->pCutArrival);
    ABC_FREE(p->pDpStart); ABC_FREE(p->pDpOrder);
    ABC_FREE(p->pBound); ABC_FREE(p->pNodeBound);
}

// Deadline-independent lower bounds on discounted costs for the current
// weights. Each candidate bound adds its leaves' bounds in the same order as
// the DP adds their costs, so float monotonicity keeps bound <= cost.
/**Function*************************************************************

  Synopsis    [Compute deadline-independent lower bounds for area-flow costs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Lmt_Bounds( Lmt_Man_t * p )
{
    Gia_Obj_t * pObj;
    int Id, c, k;
    Gia_ManForEachObj(p->pGia, pObj, Id)
    {
        float Best;
        if ( !Gia_ObjIsAnd(pObj) ) { p->pNodeBound[Id] = 0; continue; }
        Best = 1 + p->pNodeBound[Gia_ObjFaninId0p(p->pGia, pObj)] + p->pNodeBound[Gia_ObjFaninId1p(p->pGia, pObj)];
        for ( c = p->pHeads[Id]; c >= 0; c = Lmt_Next(p, c) )
        {
            Lmt_Cut_t Cut, * pCut = &Cut;
            float Bound;
            Lmt_GetCut(p, c, pCut);
            Bound = (float)pCut->Area;
            for ( k = 0; k < pCut->nLeaves; ++k ) Bound += p->pNodeBound[Abc_Lit2Var(pCut->Leaves[k])];
            p->pBound[c] = Bound;
            if ( Bound < Best ) Best = Bound;
        }
        p->pNodeBound[Id] = Best / p->pWeights[Id];
    }
}

/**Function*************************************************************

  Synopsis    [Accumulate a selected leaf's deadline and reference count.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Lmt_Require( Lmt_Man_t * p, int Id, int Required )
{
    assert(Required >= 0);
    p->pRequired[Id] = Abc_MinInt(p->pRequired[Id], Required);
    ++p->pRefs[Id];
}

/**Function*************************************************************

  Synopsis    [Resolve shared nodes using their strictest requirement.]

  Description [Reverse topological order finalizes every consumer before
  its producer. This avoids emitting two implementations of a shared node.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmt_Select( Lmt_Man_t * p )
{
    Gia_Obj_t * pObj;
    int Id, k, Count = 0;
    for ( Id = 0; Id < Gia_ManObjNum(p->pGia); ++Id )
    { p->pRequired[Id] = ABC_INFINITY; p->pRefs[Id] = 0; }
    Gia_ManForEachCo(p->pGia, pObj, Id)
    {
        int Driver = Gia_ObjFaninId0p(p->pGia, pObj);
        int Required = Lmt_CoRequired(p, Id);
        if ( Lmt_Cost(p, Driver, Required) >= 1.0e29f )
        {
            if ( p->pGia->vCiArrs || p->pGia->vCoReqs )
                Abc_Print(-1, "LMS timing: CO %d requires %d; earliest arrival in the retained bank is %d.\n", Id, Required, p->pMinArr[Driver]);
            return -1;
        }
        Lmt_Require(p, Driver, Required);
    }
    for ( Id = Gia_ManObjNum(p->pGia)-1; Id > 0; --Id )
    {
        int Choice, Required = p->pRequired[Id];
        pObj = Gia_ManObj(p->pGia, Id);
        if ( !Gia_ObjIsAnd(pObj) || Required == ABC_INFINITY ) continue;
        // Shared consumers can tighten a requirement to a slot not visited
        // while evaluating any single output. Materialize it before selection.
        if ( Lmt_Cost(p, Id, Required) >= 1.0e29f ) return -1;
        Choice = p->pChoice[Lmt_Index(p, Id, Required)];
        p->pSelected[Id] = Choice;
        if ( Choice < 0 )
        {
            Lmt_Require(p, Gia_ObjFaninId0p(p->pGia, pObj), Required-1);
            Lmt_Require(p, Gia_ObjFaninId1p(p->pGia, pObj), Required-1);
        }
        else
        {
            Lmt_Cut_t Cut, * pCut = &Cut;
            Lmt_GetCut(p, Choice, pCut);
            ++Count;
            for ( k = 0; k < pCut->nLeaves; ++k )
                Lmt_Require(p, Abc_Lit2Var(pCut->Leaves[k]), Required-pCut->Depths[k]);
        }
    }
    return Count;
}

/**Function*************************************************************

  Synopsis    [Reconstruct selected cones with exact structural sharing.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Lmt_Build( Lmt_Man_t * p )
{
    Gia_Man_t * pNew = Gia_ManStart(Gia_ManObjNum(p->pGia)), * pClean;
    Gia_Obj_t * pObj;
    int Id, k, Leaves[6];
    int * pLits = ABC_CALLOC(int, Gia_ManObjNum(p->pGia));
    Gia_ManHashAlloc(pNew);
    Gia_ManForEachObj1(p->pGia, pObj, Id)
    {
        if ( Gia_ObjIsCi(pObj) ) pLits[Id] = Gia_ManAppendCi(pNew);
        else if ( Gia_ObjIsCo(pObj) )
            Gia_ManAppendCo(pNew, Abc_LitNotCond(pLits[Gia_ObjFaninId0p(p->pGia, pObj)], Gia_ObjFaninC0(pObj)));
        else if ( p->pRequired[Id] != ABC_INFINITY )
        {
            if ( p->pSelected[Id] < 0 )
                pLits[Id] = Gia_ManHashAnd(pNew,
                    Abc_LitNotCond(pLits[Gia_ObjFaninId0p(p->pGia, pObj)], Gia_ObjFaninC0(pObj)),
                    Abc_LitNotCond(pLits[Gia_ObjFaninId1p(p->pGia, pObj)], Gia_ObjFaninC1(pObj)));
            else
            {
                Lmt_Cut_t Cut, * pCut = &Cut;
                Lmt_GetCut(p, p->pSelected[Id], pCut);
                for ( k = 0; k < pCut->nLeaves; ++k )
                    Leaves[k] = Abc_LitNotCond(pLits[Abc_Lit2Var(pCut->Leaves[k])], Abc_LitIsCompl(pCut->Leaves[k]));
                pLits[Id] = Lmt_BuildMacro(p, pNew, pCut->Po, pCut->nLeaves, Leaves, pCut->Compl);
            }
        }
    }
    Gia_ManHashStop(pNew);
    Gia_ManSetRegNum(pNew, Gia_ManRegNum(p->pGia));
    pClean = Gia_ManCleanup(pNew);
    Gia_ManStop(pNew);
    pClean->pName = Abc_UtilStrsav(p->pGia->pName);
    pClean->pSpec = Abc_UtilStrsav(p->pGia->pSpec);
    if ( p->pGia->vNamesIn ) pClean->vNamesIn = Vec_PtrDupStr(p->pGia->vNamesIn);
    if ( p->pGia->vNamesOut ) pClean->vNamesOut = Vec_PtrDupStr(p->pGia->vNamesOut);
    ABC_FREE(pLits);
    return pClean;
}

/**Function*************************************************************

  Synopsis    [Mark the live cover of a fixed set of replacements.]

  Description [Returns the number of live library replacements.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmt_Reach( Lmt_Man_t * p )
{
    Gia_Obj_t * pObj;
    int j, k, Count = 0, n = Gia_ManObjNum(p->pGia);
    for ( j = 0; j < n; ++j ) p->pRequired[j] = ABC_INFINITY;
    Gia_ManForEachCo(p->pGia, pObj, j)
        p->pRequired[Gia_ObjFaninId0p(p->pGia, pObj)] = 0;
    for ( j = n-1; j > 0; --j )
    {
        pObj = Gia_ManObj(p->pGia, j);
        if ( !Gia_ObjIsAnd(pObj) || p->pRequired[j] == ABC_INFINITY ) continue;
        if ( p->pSelected[j] < 0 )
        {
            p->pRequired[Gia_ObjFaninId0p(p->pGia, pObj)] = 0;
            p->pRequired[Gia_ObjFaninId1p(p->pGia, pObj)] = 0;
        }
        else
        {
            Lmt_Cut_t Cut, * pCut = &Cut;
            Lmt_GetCut(p, p->pSelected[j], pCut);
            ++Count;
            for ( k = 0; k < pCut->nLeaves; ++k ) p->pRequired[Abc_Lit2Var(pCut->Leaves[k])] = 0;
        }
    }
    return Count;
}

/**Function*************************************************************

  Synopsis    [Push a choice's leaves and return its local area.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmt_RefPushLeaves( Lmt_Man_t * p, int Id, int Choice )
{
    Lmt_Cut_t Cut;
    int k;
    if ( Choice < 0 )
    {
        Gia_Obj_t * pObj = Gia_ManObj(p->pGia, Id);
        Vec_IntPush(p->vRefStack, Gia_ObjFaninId1p(p->pGia, pObj));
        Vec_IntPush(p->vRefStack, Gia_ObjFaninId0p(p->pGia, pObj));
        return 1;
    }
    Lmt_GetCut(p, Choice, &Cut);
    for ( k = Cut.nLeaves-1; k >= 0; --k )
        Vec_IntPush(p->vRefStack, Abc_Lit2Var(Cut.Leaves[k]));
    return Cut.Area;
}
/**Function*************************************************************

  Synopsis    [Update cover references iteratively and count changed area.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmt_RefStack( Lmt_Man_t * p, int fRef )
{
    int Area = 0;
    while ( Vec_IntSize(p->vRefStack) )
    {
        int Id = Vec_IntPop(p->vRefStack), Old = p->pRefs[Id];
        assert(fRef || Old > 0);
        p->pRefs[Id] += fRef ? 1 : -1;
        if ( !Gia_ObjIsAnd(Gia_ManObj(p->pGia, Id)) || (fRef ? Old != 0 : Old != 1) ) continue;
        Area += Lmt_RefPushLeaves(p, Id, p->pSelected[Id]);
    }
    return Area;
}
/**Function*************************************************************

  Synopsis    [Update references below a candidate without changing its root.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmt_RefLeaves( Lmt_Man_t * p, int Id, int Choice, int fRef )
{
    int Area;
    assert(Vec_IntSize(p->vRefStack) == 0);
    Area = Lmt_RefPushLeaves(p, Id, Choice);
    return Area + Lmt_RefStack(p, fRef);
}
/**Function*************************************************************

  Synopsis    [Update references through a selected cover node.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmt_RefNode( Lmt_Man_t * p, int Id, int fRef )
{
    assert(Vec_IntSize(p->vRefStack) == 0);
    Vec_IntPush(p->vRefStack, Id);
    return Lmt_RefStack(p, fRef);
}

/**Function*************************************************************

  Synopsis    [Compute cover levels and initialize output requirements.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Lmt_Levels( Lmt_Man_t * p, int * pLevels )
{
    Gia_Obj_t * pObj;
    int Id, k;
    if ( p->pGia->vCiArrs )
        Gia_ManForEachCi(p->pGia, pObj, Id)
            pLevels[Gia_ObjId(p->pGia, pObj)] = Vec_IntEntry(p->pGia->vCiArrs, Id);
    Gia_ManForEachObj(p->pGia, pObj, Id)
    {
        p->pRequired[Id] = ABC_INFINITY;
        if ( !Gia_ObjIsAnd(pObj) ) continue;
        if ( p->pSelected[Id] < 0 )
            pLevels[Id] = Lmt_AddDelay(Abc_MaxInt(pLevels[Gia_ObjFaninId0p(p->pGia, pObj)], pLevels[Gia_ObjFaninId1p(p->pGia, pObj)]), 1);
        else
        {
            Lmt_Cut_t Cut, * pCut = &Cut;
            Lmt_GetCut(p, p->pSelected[Id], pCut);
            pLevels[Id] = 0;
            for ( k = 0; k < pCut->nLeaves; ++k )
                pLevels[Id] = Abc_MaxInt(pLevels[Id], Lmt_AddDelay(pLevels[Abc_Lit2Var(pCut->Leaves[k])], pCut->Depths[k]));
        }
    }
    Gia_ManForEachCo(p->pGia, pObj, Id)
    {
        int Driver = Gia_ObjFaninId0p(p->pGia, pObj);
        p->pRequired[Driver] = Abc_MinInt(p->pRequired[Driver], Lmt_CoRequired(p, Id));
    }
}

// Finalize each consumer once in reverse topological order. Its producers
// have not changed yet, so their initial levels remain valid for every trial.
/**Function*************************************************************

  Synopsis    [Propagate a finalized root's requirement to its chosen leaves.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Lmt_RefineRequire( Lmt_Man_t * p, int Id )
{
    Gia_Obj_t * pObj = Gia_ManObj(p->pGia, Id);
    int k, Required = p->pRequired[Id];
    if ( p->pSelected[Id] < 0 )
    {
        int i0 = Gia_ObjFaninId0p(p->pGia, pObj), i1 = Gia_ObjFaninId1p(p->pGia, pObj);
        p->pRequired[i0] = Abc_MinInt(p->pRequired[i0], Required-1);
        p->pRequired[i1] = Abc_MinInt(p->pRequired[i1], Required-1);
    }
    else
    {
        Lmt_Cut_t Cut, * pCut = &Cut;
        Lmt_GetCut(p, p->pSelected[Id], pCut);
        for ( k = 0; k < pCut->nLeaves; ++k )
        {
            int Leaf = Abc_Lit2Var(pCut->Leaves[k]);
            p->pRequired[Leaf] = Abc_MinInt(p->pRequired[Leaf], Required-pCut->Depths[k]);
        }
    }
}

/**Function*************************************************************

  Synopsis    [Compare a timing-feasible candidate's referenced cover area.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Lmt_RefineTry( Lmt_Man_t * p, int Id, int Choice, int Required,
    int * pLevels, int * pBest, int * pAreaBest )
{
    int k, Arrival = 0, Area;
    if ( Choice < 0 )
    {
        Gia_Obj_t * pObj = Gia_ManObj(p->pGia, Id);
        Arrival = Lmt_AddDelay(Abc_MaxInt(pLevels[Gia_ObjFaninId0p(p->pGia, pObj)], pLevels[Gia_ObjFaninId1p(p->pGia, pObj)]), 1);
    }
    else
    {
        Lmt_Cut_t Cut, * pCut = &Cut;
        Lmt_GetCut(p, Choice, pCut);
        for ( k = 0; k < pCut->nLeaves; ++k )
            Arrival = Abc_MaxInt(Arrival, Lmt_AddDelay(pLevels[Abc_Lit2Var(pCut->Leaves[k])], pCut->Depths[k]));
    }
    if ( Arrival > Required ) return;
    Area = Lmt_RefLeaves(p, Id, Choice, 1);
    Lmt_RefLeaves(p, Id, Choice, 0);
    if ( Area < *pAreaBest ) { *pAreaBest = Area; *pBest = Choice; }
}
/**Function*************************************************************

  Synopsis    [Refine selected roots using reference-counted cone costs.]

  Description [This is our own fixed-bank sweep, not mapper recovery.
  Costs are exact for the cover of library macros, but do not predict
  hashing between macro interiors. The entire sweep is rolled back if
  measured live AIG area increases or the timing target is missed.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Lmt_Refine( Lmt_Man_t * p, Gia_Man_t * pBest, int fVerbose )
{
    Gia_Obj_t * pObj;
    Gia_Man_t * pTrial;
    int Id, c, Changed = 0, n = Gia_ManObjNum(p->pGia);
    int * pLevels = ABC_CALLOC(int, n), * pSaved = ABC_ALLOC(int, n);
    for ( Id = 0; Id < n; ++Id )
    {
        if ( p->pRequired[Id] == ABC_INFINITY ) p->pSelected[Id] = -1;
        p->pRefs[Id] = 0;
    }
    memcpy(pSaved, p->pSelected, sizeof(int)*n);
    Gia_ManForEachCo(p->pGia, pObj, Id) Lmt_RefNode(p, Gia_ObjFaninId0p(p->pGia, pObj), 1);
    Lmt_Levels(p, pLevels);
    for ( Id = n-1; Id > 0; --Id )
    {
        int Best, AreaBest, Required = p->pRequired[Id];
        if ( !p->pRefs[Id] || !Gia_ObjIsAnd(Gia_ManObj(p->pGia, Id)) ) continue;
        Best = p->pSelected[Id];
        AreaBest = Lmt_RefLeaves(p, Id, Best, 0);
        // The detached baseline lets references measure each candidate's
        // newly live cone, including reuse of already-live cut leaves.
        Lmt_RefineTry(p, Id, -1, Required, pLevels, &Best, &AreaBest);
        for ( c = p->pHeads[Id]; c >= 0; c = Lmt_Next(p, c) )
            Lmt_RefineTry(p, Id, c, Required, pLevels, &Best, &AreaBest);
        Lmt_RefLeaves(p, Id, Best, 1);
        if ( Best != p->pSelected[Id] )
        { p->pSelected[Id] = Best; ++Changed; }
        Lmt_RefineRequire(p, Id);
    }
    Lmt_Reach(p);
    pTrial = Lmt_Build(p);
    if ( Gia_ManAndNum(pTrial) <= Gia_ManAndNum(pBest) && Lmt_CheckTiming(p, pTrial) )
    { Gia_ManStop(pBest); pBest = pTrial; }
    else
    { Gia_ManStop(pTrial); memcpy(p->pSelected, pSaved, sizeof(int)*n); Changed = 0; Lmt_Reach(p); }
    if ( fVerbose ) Abc_Print(1, "LMS target refine: %d changes accepted; %d ANDs, depth %d.\n",
        Changed, Gia_ManAndNum(pBest), Gia_ManLevelNum(pBest));
    ABC_FREE(pLevels);
    ABC_FREE(pSaved);
    return pBest;
}

/**Function*************************************************************

  Synopsis    [Extend reference and timing arrays for newly hashed nodes.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Lmt_UnionGrow( Lmt_Union_t * u )
{
    int Id, nOld = Vec_IntSize(u->vLevels), n = Gia_ManObjNum(u->pGraph);
    Vec_IntFillExtra(u->vRefs, n, 0);
    Vec_IntFillExtra(u->vSeen, 2*n, 0);
    Vec_IntFillExtra(u->vReq, n, ABC_INFINITY);
    Vec_IntFillExtra(u->vLevels, n, 0);
    Vec_IntFillExtra(u->vProbeMark, n, 0);
    for ( Id = nOld; Id < n; ++Id )
    {
        Gia_Obj_t * pObj = Gia_ManObj(u->pGraph, Id);
        if ( Gia_ObjIsCi(pObj) && u->p->pGia->vCiArrs )
            Vec_IntWriteEntry(u->vLevels, Id, Vec_IntEntry(u->p->pGia->vCiArrs, Gia_ObjCioId(pObj)));
        else if ( Gia_ObjIsAnd(pObj) )
            Vec_IntWriteEntry(u->vLevels, Id, Lmt_AddDelay(Abc_MaxInt(
                Vec_IntEntry(u->vLevels, Gia_ObjFaninId0p(u->pGraph, pObj)),
                Vec_IntEntry(u->vLevels, Gia_ObjFaninId1p(u->pGraph, pObj))), 1));
    }
}

// References count only live physical AND edges and output uses, never the
// logical cut boundaries or the inactive candidate roots in the union.
/**Function*************************************************************

  Synopsis    [Update live physical references and area without recursion.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Lmt_UnionRef( Lmt_Union_t * u, int Lit, int fRef )
{
    Vec_IntPush(u->vStack, Abc_Lit2Var(Lit));
    while ( Vec_IntSize(u->vStack) )
    {
        int Id = Vec_IntPop(u->vStack), Old = Vec_IntEntry(u->vRefs, Id);
        Gia_Obj_t * pObj = Gia_ManObj(u->pGraph, Id);
        assert(fRef || Old > 0);
        Vec_IntWriteEntry(u->vRefs, Id, Old + (fRef ? 1 : -1));
        if ( (fRef ? Old != 0 : Old != 1) || !Gia_ObjIsAnd(pObj) ) continue;
        u->Area += fRef ? 1 : -1;
        Vec_IntPush(u->vStack, Gia_ObjFaninId0p(u->pGraph, pObj));
        Vec_IntPush(u->vStack, Gia_ObjFaninId1p(u->pGraph, pObj));
    }
}

/**Function*************************************************************

  Synopsis    [Hash a selected implementation using current leaf literals.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmt_UnionBuild( Lmt_Union_t * u, int Id, int Choice )
{
    Lmt_Cut_t Cut;
    Gia_Obj_t * pObj = Gia_ManObj(u->p->pGia, Id);
    int k, Leaves[6];
    if ( Gia_ObjIsCo(pObj) )
        return Abc_LitNotCond(u->pLits[Gia_ObjFaninId0p(u->p->pGia, pObj)], Gia_ObjFaninC0(pObj));
    if ( Choice < 0 )
        return Gia_ManHashAnd(u->pGraph,
            Abc_LitNotCond(u->pLits[Gia_ObjFaninId0p(u->p->pGia, pObj)], Gia_ObjFaninC0(pObj)),
            Abc_LitNotCond(u->pLits[Gia_ObjFaninId1p(u->p->pGia, pObj)], Gia_ObjFaninC1(pObj)));
    Lmt_GetCut(u->p, Choice, &Cut);
    for ( k = 0; k < Cut.nLeaves; ++k )
        Leaves[k] = Abc_LitNotCond(u->pLits[Abc_Lit2Var(Cut.Leaves[k])], Abc_LitIsCompl(Cut.Leaves[k]));
    return Lmt_BuildMacro(u->p, u->pGraph, Cut.Po, Cut.nLeaves, Leaves, Cut.Compl);
}

/**Function*************************************************************

  Synopsis    [Queue an inactive node whose cached literal is stale.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Lmt_UnionRefreshPush( Lmt_Union_t * u, int Id )
{
    if ( u->p->pRefs[Id] || u->pFresh[Id] == u->nChanges+1 || !Gia_ObjIsAnd(Gia_ManObj(u->p->pGia, Id)) ) return;
    Vec_IntPush(u->vRefresh, Id);
}
/**Function*************************************************************

  Synopsis    [Queue stale leaves of an original gate or library choice.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Lmt_UnionPushLeaves( Lmt_Union_t * u, int Id, int Choice )
{
    Lmt_Cut_t Cut;
    Gia_Obj_t * pObj = Gia_ManObj(u->p->pGia, Id);
    int k;
    if ( Choice < 0 )
    {
        Lmt_UnionRefreshPush(u, Gia_ObjFaninId0p(u->p->pGia, pObj));
        Lmt_UnionRefreshPush(u, Gia_ObjFaninId1p(u->p->pGia, pObj));
    }
    else
    {
        Lmt_GetCut(u->p, Choice, &Cut);
        for ( k = 0; k < Cut.nLeaves; ++k )
            Lmt_UnionRefreshPush(u, Abc_Lit2Var(Cut.Leaves[k]));
    }
}

// Dirty propagation updates live consumers only. Refresh inactive dependency
// cones before a trial can make them live again; never bind an obsolete copy.
/**Function*************************************************************

  Synopsis    [Rebuild stale inactive fanin cones before a union trial.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Lmt_UnionRefresh( Lmt_Union_t * u, int Root, int Choice )
{
    int Id, Epoch = u->nChanges+1;
    assert(Vec_IntSize(u->vRefresh) == 0);
    Lmt_UnionPushLeaves(u, Root, Choice);
    while ( Vec_IntSize(u->vRefresh) )
    {
        Id = Vec_IntPop(u->vRefresh);
        if ( Id < 0 )
        {
            Id = ~Id;
            u->pLits[Id] = Lmt_UnionBuild(u, Id, u->p->pSelected[Id]);
            u->pFresh[Id] = Epoch;
            continue;
        }
        if ( u->p->pRefs[Id] || u->pFresh[Id] == Epoch || !Gia_ObjIsAnd(Gia_ManObj(u->p->pGia, Id)) ) continue;
        Vec_IntPush(u->vRefresh, ~Id);
        Lmt_UnionPushLeaves(u, Id, u->p->pSelected[Id]);
    }
    Lmt_UnionGrow(u);
}

// Bound inactive trial storage by occasionally reseeding the persistent hash
// from the current logical cover. This is not done for individual trials.
/**Function*************************************************************

  Synopsis    [Rebuild the union from selected implementations and live outputs.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Lmt_UnionSeed( Lmt_Union_t * u )
{
    Gia_Obj_t * pObj;
    int Id;
    if ( u->pGraph ) { Gia_ManStop(u->pGraph); ++u->nRebases; }
    u->pGraph = Gia_ManStart(Gia_ManObjNum(u->p->pGia));
    Gia_ManHashAlloc(u->pGraph);
    Vec_IntClear(u->vRefs);
    Vec_IntClear(u->vLevels);
    Vec_IntClear(u->vSeen);
    Vec_IntClear(u->vProbeMark);
    u->Area = 0;
    u->pLits[0] = 0;
    Gia_ManForEachObj1(u->p->pGia, pObj, Id)
    {
        u->pLits[Id] = Gia_ObjIsCi(pObj) ? Gia_ManAppendCi(u->pGraph)
            : Lmt_UnionBuild(u, Id, u->p->pSelected[Id]);
        u->pFresh[Id] = u->nChanges+1;
    }
    Lmt_UnionGrow(u);
    Gia_ManForEachCo(u->p->pGia, pObj, Id)
        Lmt_UnionRef(u, u->pLits[Gia_ObjId(u->p->pGia, pObj)], 1);
    // A large live seed must not trigger another reseed at every candidate.
    u->RebaseAt = Abc_MaxInt(LMS_TARGET_UNION_LIMIT,
        Gia_ManObjNum(u->pGraph) + Abc_MaxInt(1024, Gia_ManObjNum(u->pGraph)/2));
    u->fReqDirty = 1;
}

// Required times on the actual live physical graph, without scanning inactive
// alternatives. Temporarily negating positive refs provides a DFS visit mark.
// Exit markers produce fanin-first postorder; traversing it backward avoids
// sorting all live node IDs after every accepted change.
/**Function*************************************************************

  Synopsis    [Compute required times on the live physical graph.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmt_UnionRequired( Lmt_Union_t * u, int Root )
{
    Gia_Obj_t * pObj;
    int Id, i;
    if ( !u->fReqDirty ) return Vec_IntEntry(u->vReq, Abc_Lit2Var(u->pLits[Root]));
    Vec_IntClear(u->vLive);
    Gia_ManForEachCo(u->p->pGia, pObj, i)
        Vec_IntPush(u->vStack, Abc_Lit2Var(u->pLits[Gia_ObjId(u->p->pGia, pObj)]));
    while ( Vec_IntSize(u->vStack) )
    {
        Id = Vec_IntPop(u->vStack);
        if ( Id < 0 ) { Vec_IntPush(u->vLive, ~Id); continue; }
        if ( Vec_IntEntry(u->vRefs, Id) < 0 ) continue;
        assert(Vec_IntEntry(u->vRefs, Id) > 0);
        Vec_IntWriteEntry(u->vRefs, Id, -Vec_IntEntry(u->vRefs, Id));
        Vec_IntPush(u->vStack, ~Id);
        pObj = Gia_ManObj(u->pGraph, Id);
        if ( !Gia_ObjIsAnd(pObj) ) continue;
        Vec_IntPush(u->vStack, Gia_ObjFaninId0p(u->pGraph, pObj));
        Vec_IntPush(u->vStack, Gia_ObjFaninId1p(u->pGraph, pObj));
    }
    Vec_IntForEachEntry(u->vLive, Id, i)
    {
        Vec_IntWriteEntry(u->vRefs, Id, -Vec_IntEntry(u->vRefs, Id));
        Vec_IntWriteEntry(u->vReq, Id, ABC_INFINITY);
    }
    Gia_ManForEachCo(u->p->pGia, pObj, i)
    {
        int Driver = Abc_Lit2Var(u->pLits[Gia_ObjId(u->p->pGia, pObj)]);
        Vec_IntWriteEntry(u->vReq, Driver, Abc_MinInt(Vec_IntEntry(u->vReq, Driver), Lmt_CoRequired(u->p, i)));
    }
    Vec_IntForEachEntryReverse(u->vLive, Id, i)
    {
        int Required = Vec_IntEntry(u->vReq, Id), i0, i1;
        pObj = Gia_ManObj(u->pGraph, Id);
        if ( !Gia_ObjIsAnd(pObj) ) continue;
        i0 = Gia_ObjFaninId0p(u->pGraph, pObj); i1 = Gia_ObjFaninId1p(u->pGraph, pObj);
        Vec_IntWriteEntry(u->vReq, i0, Abc_MinInt(Vec_IntEntry(u->vReq, i0), Required-1));
        Vec_IntWriteEntry(u->vReq, i1, Abc_MinInt(Vec_IntEntry(u->vReq, i1), Required-1));
    }
    u->fReqDirty = 0;
    return Vec_IntEntry(u->vReq, Abc_Lit2Var(u->pLits[Root]));
}

/**Function*************************************************************

  Synopsis    [Add or remove the current logical dependency edges.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Lmt_UnionFanouts( Lmt_Union_t * u, int Id, int Choice, int fAdd )
{
    Lmt_Man_t * p = u->p;
    Gia_Obj_t * pObj = Gia_ManObj(p->pGia, Id);
    int k, j, n, Leaves[6];
    if ( Gia_ObjIsCo(pObj) || Choice < 0 )
    {
        Leaves[0] = Gia_ObjFaninId0p(p->pGia, pObj);
        n = Gia_ObjIsCo(pObj) ? 1 : 2;
        if ( n == 2 ) Leaves[1] = Gia_ObjFaninId1p(p->pGia, pObj);
    }
    else
    {
        Lmt_Cut_t Cut;
        Lmt_GetCut(p, Choice, &Cut);
        n = Cut.nLeaves;
        for ( k = 0; k < n; ++k ) Leaves[k] = Abc_Lit2Var(Cut.Leaves[k]);
    }
    for ( k = 0; k < n; ++k )
    {
        for ( j = 0; j < k; ++j ) if ( Leaves[j] == Leaves[k] ) break;
        if ( j < k ) continue;
        if ( fAdd ) Vec_WecPush(u->vFanouts, Leaves[k], Id);
        else
        {
            int Removed = Vec_IntRemove(Vec_WecEntry(u->vFanouts, Leaves[k]), Id);
            assert(Removed);
            (void)Removed;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Collect affected live fanouts in topological order.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Lmt_UnionDirty( Lmt_Union_t * u, int Root )
{
    int i, k, Id, Fanout;
    Vec_IntClear(u->vDirty);
    Vec_IntPush(u->vDirty, Root);
    u->pMarks[Root] = Root;
    Vec_IntForEachEntry(u->vDirty, Id, i)
        Vec_IntForEachEntry(Vec_WecEntry(u->vFanouts, Id), Fanout, k)
            if ( u->pMarks[Fanout] != Root && (u->p->pRefs[Fanout] || Gia_ObjIsCo(Gia_ManObj(u->p->pGia, Fanout))) )
            { u->pMarks[Fanout] = Root; Vec_IntPush(u->vDirty, Fanout); }
    Vec_IntSort(u->vDirty, 0);
    u->DirtyRoot = Root;
}

#ifdef LMS_TARGET_CHECK_UNION
/**Function*************************************************************

  Synopsis    [Check incremental references and area against reconstruction.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Lmt_UnionCheck( Lmt_Union_t * u )
{
    Gia_Obj_t * pObj;
    Gia_Man_t * pCheck;
    int Id, Area = 0, n = Gia_ManObjNum(u->pGraph);
    int * pRefs = ABC_CALLOC(int, n);
    Gia_ManForEachCo(u->p->pGia, pObj, Id)
        ++pRefs[Abc_Lit2Var(u->pLits[Gia_ObjId(u->p->pGia, pObj)])];
    for ( Id = n-1; Id > 0; --Id )
        if ( pRefs[Id] && Gia_ObjIsAnd(Gia_ManObj(u->pGraph, Id)) )
        {
            pObj = Gia_ManObj(u->pGraph, Id);
            ++pRefs[Gia_ObjFaninId0p(u->pGraph, pObj)];
            ++pRefs[Gia_ObjFaninId1p(u->pGraph, pObj)];
            ++Area;
        }
    for ( Id = 0; Id < n; ++Id ) assert(pRefs[Id] == Vec_IntEntry(u->vRefs, Id));
    assert(Area == u->Area);
    ABC_FREE(pRefs);
    Lmt_Reach(u->p);
    pCheck = Lmt_Build(u->p);
    assert(Gia_ManAndNum(pCheck) == u->Area);
    assert(Lmt_CheckTiming(u->p, pCheck));
    Gia_ManStop(pCheck);
}
#endif

/**Function*************************************************************

  Synopsis    [Price a replacement by its actual live hashed AND count.]

  Description [Rebind the affected selected fanout cone in the persistent
  union. Reference/dereference only changed output cones. Rejected trials
  restore bindings and references, but their inactive hashed nodes remain
  reusable. No full AIG reconstruction or cleanup is needed per trial.]

  SideEffects [Accepts only feasible, non-growing physical implementations.]

  SeeAlso     [Lmt_UnionRecover]

***********************************************************************/
static void Lmt_UnionTry( Lmt_Union_t * u, int Root, int Choice )
{
    Lmt_Man_t * p = u->p;
    int i, Id, Lit, Before, Bad = 0, Accept;
    if ( Lmt_SameChoice(p, Choice, p->pSelected[Root]) ) { ++u->nCurrent; return; }
    if ( Gia_ManObjNum(u->pGraph) > u->RebaseAt ) Lmt_UnionSeed(u);
    Before = u->Area;
    Lmt_UnionRefresh(u, Root, Choice);
    Lit = Lmt_UnionBuild(u, Root, Choice);
    Lmt_UnionGrow(u);
    ++u->nCandidates;
    if ( Vec_IntEntry(u->vSeen, Lit) == Root ) return;
    Vec_IntWriteEntry(u->vSeen, Lit, Root);
    if ( Lit == u->pLits[Root] && Choice >= 0 ) return;
    ++u->nTrials;
    // The affected fanout cone depends only on nodes above the root, which
    // no accepted change at this root alters; compute it at first real use.
    if ( u->DirtyRoot != Root ) Lmt_UnionDirty(u, Root);
    if ( u->Stamp == ABC_INFINITY )
    { memset(u->pChanged, 0, sizeof(int)*Gia_ManObjNum(p->pGia)); u->Stamp = 0; }
    ++u->Stamp;
    Vec_IntClear(u->vSaved);
    Vec_IntForEachEntry(u->vDirty, Id, i)
    {
        Gia_Obj_t * pObj = Gia_ManObj(p->pGia, Id);
        int k, Changed = Id == Root;
        Vec_IntPush(u->vSaved, u->pLits[Id]);
        if ( !Changed && (Gia_ObjIsCo(pObj) || p->pSelected[Id] < 0) )
            Changed = u->pChanged[Gia_ObjFaninId0p(p->pGia, pObj)] == u->Stamp ||
                (Gia_ObjIsAnd(pObj) && u->pChanged[Gia_ObjFaninId1p(p->pGia, pObj)] == u->Stamp);
        else if ( !Changed )
        {
            Lmt_Cut_t Cut;
            Lmt_GetCut(p, p->pSelected[Id], &Cut);
            for ( k = 0; k < Cut.nLeaves; ++k )
                Changed |= u->pChanged[Abc_Lit2Var(Cut.Leaves[k])] == u->Stamp;
        }
        if ( Changed )
        {
            u->pLits[Id] = Id == Root ? Lit : Lmt_UnionBuild(u, Id, p->pSelected[Id]);
            if ( u->pLits[Id] != Vec_IntEntry(u->vSaved, i) ) u->pChanged[Id] = u->Stamp;
        }
    }
    Lmt_UnionGrow(u);
    u->nTouched += Vec_IntSize(u->vDirty);
    Vec_IntForEachEntry(u->vDirty, Id, i)
        if ( Gia_ObjIsCo(Gia_ManObj(p->pGia, Id)) &&
            Vec_IntEntry(u->vLevels, Abc_Lit2Var(u->pLits[Id])) > Lmt_CoRequired(p, Gia_ObjCioId(Gia_ManObj(p->pGia, Id))) ) Bad = 1;
    if ( !Bad )
        Vec_IntForEachEntry(u->vDirty, Id, i)
            if ( Gia_ObjIsCo(Gia_ManObj(p->pGia, Id)) && u->pLits[Id] != Vec_IntEntry(u->vSaved, i) )
            {
                // Keep common subgraphs live instead of dropping and then
                // traversing them again when the replacement shares them.
                Lmt_UnionRef(u, u->pLits[Id], 1);
                Lmt_UnionRef(u, Vec_IntEntry(u->vSaved, i), 0);
            }
    Accept = !Bad && (u->Area < Before || (u->Area == Before && Choice < 0));
    if ( Accept )
    {
        Lmt_RefLeaves(p, Root, p->pSelected[Root], 0);
        Lmt_RefLeaves(p, Root, Choice, 1);
        Lmt_UnionFanouts(u, Root, p->pSelected[Root], 0);
        p->pSelected[Root] = Choice;
        Lmt_UnionFanouts(u, Root, Choice, 1);
        u->fReqDirty = 1;
        ++u->nChanges;
    }
    else
    {
        Vec_IntForEachEntry(u->vDirty, Id, i)
        {
            if ( !Bad && Gia_ObjIsCo(Gia_ManObj(p->pGia, Id)) && u->pLits[Id] != Vec_IntEntry(u->vSaved, i) )
            {
                Lmt_UnionRef(u, Vec_IntEntry(u->vSaved, i), 1);
                Lmt_UnionRef(u, u->pLits[Id], 0);
            }
            u->pLits[Id] = Vec_IntEntry(u->vSaved, i);
        }
        assert(u->Area == Before);
    }
#ifdef LMS_TARGET_CHECK_UNION
    Lmt_UnionCheck(u);
#endif
}

// Lookup-only hashing: absent nodes get virtual labels, merged by fanin pair
// exactly as Gia_ManHashAnd would merge them once inserted.
/**Function*************************************************************

  Synopsis    [Probe structural hashing with temporary labels for absent nodes.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmt_VirtAnd( Lmt_Union_t * u, int a, int b )
{
    int i, r, Base = Gia_ManObjNum(u->pGraph);
    if ( a < 2 ) return a ? b : 0;
    if ( b < 2 ) return b ? a : 0;
    if ( a == b ) return a;
    if ( a == Abc_LitNot(b) ) return 0;
    if ( a > b ) { int t = a; a = b; b = t; }
    if ( Abc_Lit2Var(b) < Base && (r = Gia_ManHashAndTry(u->pGraph, a, b)) >= 0 ) return r;
    for ( i = 0; i < Vec_IntSize(u->vVirt); i += 2 )
        if ( Vec_IntEntry(u->vVirt, i) == a && Vec_IntEntry(u->vVirt, i+1) == b )
            return Abc_Var2Lit(Base + i/2, 0);
    Vec_IntPushTwo(u->vVirt, a, b);
    return Abc_Var2Lit(Base + Vec_IntSize(u->vVirt)/2 - 1, 0);
}

/**Function*************************************************************

  Synopsis    [Count the live ANDs that binding a candidate would add.]

  Description [Exact in the current reference state, without inserting
  anything into the union. Stops early once the count reaches Limit, so
  with the root detached a result >= Limit means the candidate cannot
  have a negative local cost and would never be tried.]

  SideEffects []

  SeeAlso     [Lmt_UnionRank]

***********************************************************************/
static int Lmt_UnionProbe( Lmt_Union_t * u, int Choice, int Limit )
{
    Lmt_Man_t * p = u->p;
    Lmt_Cut_t Cut, * pCut = &Cut;
    int i, k, n, Po, Out, Count = 0, Total = 0, Offset, * pCode, * pLabels;
    int Leaves[6];
    int Base = Gia_ManObjNum(u->pGraph);
    if ( !Limit ) return 0;
    Lmt_GetCut(p, Choice, pCut);
    n = pCut->nLeaves; Po = pCut->Po;
    for ( k = 0; k < n; ++k )
        Leaves[k] = Abc_LitNotCond(u->pLits[Abc_Lit2Var(pCut->Leaves[k])], Abc_LitIsCompl(pCut->Leaves[k]));
    Vec_IntClear(u->vVirt);
    if ( Po == -2 ) Out = Lmt_VirtAnd(u, Leaves[0], Leaves[1]);
    else if ( Po < 0 ) Out = n ? Leaves[0] : 0;
    else
    {
        Vec_IntFillExtra(p->vProgramOffsets, Po+1, -1);
        Offset = Vec_IntEntry(p->vProgramOffsets, Po);
        if ( Offset < 0 )
        {
            Offset = Vec_IntSize(p->vPrograms);
            Abc_RecTargetRecipe3(Po, p->vPrograms);
            Vec_IntWriteEntry(p->vProgramOffsets, Po, Offset);
        }
        pCode = Vec_IntArray(p->vPrograms)+Offset;
        Count = *pCode++;
        Vec_IntFill(p->vLabels, 6+Count, 0);
        pLabels = Vec_IntArray(p->vLabels);
        for ( i = 0; i < n; ++i ) pLabels[i] = Leaves[i];
        for ( i = 0; i < Count; ++i )
            pLabels[6+i] = Lmt_VirtAnd(u,
                Abc_LitNotCond(pLabels[Abc_Lit2Var(pCode[2*i])], Abc_LitIsCompl(pCode[2*i])),
                Abc_LitNotCond(pLabels[Abc_Lit2Var(pCode[2*i+1])], Abc_LitIsCompl(pCode[2*i+1])));
        Out = pLabels[Abc_Lit2Var(pCode[2*Count])];
    }
    Vec_IntFill(u->vVirtMark, Vec_IntSize(u->vVirt)/2, 0);
    if ( u->ProbeStamp == ABC_INFINITY )
    { Vec_IntFill(u->vProbeMark, Base, 0); u->ProbeStamp = 0; }
    ++u->ProbeStamp;
    Vec_IntClear(u->vProbeStack);
    Vec_IntPush(u->vProbeStack, Abc_Lit2Var(Out));
    while ( Vec_IntSize(u->vProbeStack) )
    {
        int v = Vec_IntPop(u->vProbeStack);
        if ( v >= Base )
        {
            if ( Vec_IntEntry(u->vVirtMark, v-Base) ) continue;
            Vec_IntWriteEntry(u->vVirtMark, v-Base, 1);
            if ( ++Total >= Limit ) return Total;
            Vec_IntPush(u->vProbeStack, Abc_Lit2Var(Vec_IntEntry(u->vVirt, 2*(v-Base))));
            Vec_IntPush(u->vProbeStack, Abc_Lit2Var(Vec_IntEntry(u->vVirt, 2*(v-Base)+1)));
        }
        else
        {
            Gia_Obj_t * pObj = Gia_ManObj(u->pGraph, v);
            if ( !Gia_ObjIsAnd(pObj) || Vec_IntEntry(u->vRefs, v) > 0 ) continue;
            if ( Vec_IntEntry(u->vProbeMark, v) == u->ProbeStamp ) continue;
            Vec_IntWriteEntry(u->vProbeMark, v, u->ProbeStamp);
            if ( ++Total >= Limit ) return Total;
            Vec_IntPush(u->vProbeStack, Gia_ObjFaninId0p(u->pGraph, pObj));
            Vec_IntPush(u->vProbeStack, Gia_ObjFaninId1p(u->pGraph, pObj));
        }
    }
    return Total;
}

/**Function*************************************************************

  Synopsis    [Shortlist locally cheap structures for exact transactions.]

  Description [The score is reference-counted cone cost with the old root
  detached. It is only a ranking: changed fanout hashing can alter the global
  cost. Predicted late and locally non-improving candidates are omitted as
  heuristics: hashing may simplify a bound structure or its fanout. Every
  accepted edit still passes the exact transaction above. Zero shortlist
  size disables ranking and both prefilters.]

  SideEffects []

  SeeAlso     [Lmt_UnionTry]

***********************************************************************/
static void Lmt_UnionRank( Lmt_Union_t * u, int Root, Lmt_Rank_t * pRank )
{
    Lmt_Man_t * p = u->p;
    int c, nRank = 0, Required, Limit = u->p->Exact;
    int OldLit, OldId, Refs, Before, Freed, PrevOwner = -1;
    int fGroups = p->nAlternatives > (size_t)p->nBaseCuts;
    if ( !Vec_IntEntry(u->vRefs, Abc_Lit2Var(u->pLits[Root])) ) return;
    if ( Gia_ManObjNum(u->pGraph) > u->RebaseAt ) Lmt_UnionSeed(u);
    Required = Lmt_UnionRequired(u, Root);
    // Detach the current root once; every candidate is priced in this state.
    OldLit = u->pLits[Root]; OldId = Abc_Lit2Var(OldLit); Refs = Vec_IntEntry(u->vRefs, OldId); Before = u->Area;
    assert(Refs > 0);
    Vec_IntWriteEntry(u->vRefs, OldId, 1);
    Lmt_UnionRef(u, OldLit, 0);
    Freed = Before - u->Area;
    for ( c = u->p->pHeads[Root]; c >= 0; c = Lmt_Next(u->p, c) )
    {
        int Lit, Cost, Added, Level = -1, Pos, i, Owner, Group = -1, Repr;
        if ( Lmt_SameChoice(p, c, p->pSelected[Root]) ) { ++u->nCurrent; continue; }
        if ( Gia_ManObjNum(u->pGraph) > u->RebaseAt )
        {
            Lmt_UnionSeed(u);
            Before = u->Area;
            Required = Lmt_UnionRequired(u, Root);
            PrevOwner = -1; // refreshed physical leaves may have new levels
            // Preserve shortlist deduplication across garbage collection.
            // Otherwise another PO with the same bound structure could use
            // a second shortlist slot merely because its literal ID changed.
            for ( i = 0; i < nRank; ++i )
            {
                int Kept;
                Lmt_UnionRefresh(u, Root, pRank[i].Choice);
                Kept = Lmt_UnionBuild(u, Root, pRank[i].Choice);
                Lmt_UnionGrow(u);
                Vec_IntWriteEntry(u->vSeen, Kept, -Root);
            }
            OldLit = u->pLits[Root]; OldId = Abc_Lit2Var(OldLit); Refs = Vec_IntEntry(u->vRefs, OldId);
            Vec_IntWriteEntry(u->vRefs, OldId, 1);
            Lmt_UnionRef(u, OldLit, 0);
            Freed = Before - u->Area;
        }
        // Binding groups are contiguous, but POs from different profiles may
        // interleave within one binding. Cache by representative while keeping
        // the original PO order and its shortlist tie-break unchanged.
        // The built-in library currently has unique profiles; it needs no
        // cache bookkeeping. External libraries may have grouped alternatives.
        if ( fGroups )
        {
            Owner = Lmt_Owner(p, c);
            if ( Owner != PrevOwner )
            { Vec_IntClear(u->vGroupLevels); PrevOwner = Owner; }
            Repr = c < p->nBaseCuts ? c : p->pExtras[c-p->nBaseCuts].Repr;
            Group = Repr-p->pBinds[Owner].First;
            assert(Group >= 0 && Lmt_Owner(p, Repr) == Owner);
            Vec_IntFillExtra(u->vGroupLevels, Group+1, -1);
            Level = Vec_IntEntry(u->vGroupLevels, Group);
        }
        if ( Level < 0 )
        {
            Lmt_Cut_t Cut, * pCut = &Cut;
            Lmt_GetCut(p, c, pCut);
            Lmt_UnionRefresh(u, Root, c);
            Level = 0;
            for ( i = 0; i < pCut->nLeaves; ++i )
                Level = Abc_MaxInt(Level, Lmt_AddDelay(
                    Vec_IntEntry(u->vLevels, Abc_Lit2Var(u->pLits[Abc_Lit2Var(pCut->Leaves[i])])), pCut->Depths[i]));
            if ( fGroups ) Vec_IntWriteEntry(u->vGroupLevels, Group, Level);
            ++u->nProfiles;
        }
        // Avoid all structures of a clearly late profile in shortlist mode.
        // This is an upper estimate if leaves alias or hashing simplifies;
        // exhaustive mode deliberately bypasses this quality/time tradeoff.
        if ( Level > Required ) { ++u->nLate; continue; }
        // Nonnegative local costs are never tried below; find them without
        // inserting anything, and bind only the candidates that can win.
        Added = Lmt_UnionProbe(u, c, Freed);
#ifdef LMS_TARGET_CHECK_UNION
        // Private oracle: validate early rejections as well as survivors.
        // Only test builds insert the otherwise rejected inactive nodes.
        Lit = Lmt_UnionBuild(u, Root, c);
        Lmt_UnionGrow(u);
        Lmt_UnionRef(u, Lit, 1);
        Cost = u->Area - Before + Freed;
        Lmt_UnionRef(u, Lit, 0);
        assert(Added == Abc_MinInt(Cost, Freed));
#endif
        if ( Added >= Freed ) { ++u->nNonnegative; continue; }
        Lit = Lmt_UnionBuild(u, Root, c);
        Lmt_UnionGrow(u);
        ++u->nCandidates;
        if ( Vec_IntEntry(u->vSeen, Lit) == -Root ) continue;
        Vec_IntWriteEntry(u->vSeen, Lit, -Root);
        Level = Vec_IntEntry(u->vLevels, Abc_Lit2Var(Lit));
        if ( Level > Required || Lit == u->pLits[Root] ) continue;
        Lmt_UnionRef(u, Lit, 1);
        Cost = u->Area - Before;
        Lmt_UnionRef(u, Lit, 0);
        assert(Cost < 0);
        assert(Cost == Added - Freed);
        // A rebase clears physical-literal marks. Do not duplicate a saved
        // candidate if an equal structure is encountered again afterward.
        for ( i = 0; i < nRank; ++i ) if ( pRank[i].Choice == c ) break;
        if ( i < nRank ) continue;
        for ( Pos = 0; Pos < nRank; ++Pos )
            if ( Cost < pRank[Pos].Cost || (Cost == pRank[Pos].Cost && Level < pRank[Pos].Level) ) break;
        if ( Pos == Limit ) continue;
        if ( nRank < Limit ) ++nRank;
        for ( i = nRank-1; i > Pos; --i ) pRank[i] = pRank[i-1];
        pRank[Pos].Choice = c; pRank[Pos].Cost = Cost; pRank[Pos].Level = Level;
    }
    Lmt_UnionRef(u, OldLit, 1);
    Vec_IntWriteEntry(u->vRefs, OldId, Refs);
    assert(u->Area == Before);
#ifdef LMS_TARGET_CHECK_UNION
    Lmt_UnionCheck(u);
#endif
    for ( c = 0; c < nRank; ++c )
    {
        // A local nonnegative score seldom benefits from the full fanout
        // transaction. It is not a lower bound on global cost, so keep this
        // pruning confined to the heuristic mode (and always try originals).
        assert(pRank[c].Cost < 0);
        Lmt_UnionTry(u, Root, pRank[c].Choice);
    }
}

/**Function*************************************************************

  Synopsis    [Order expanded alternatives by binding and decreasing output.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmt_AltCompare( const void * pA, const void * pB )
{
    const Lmt_Alt_t * a = (const Lmt_Alt_t *)pA, * b = (const Lmt_Alt_t *)pB;
    if ( a->Group != b->Group ) return a->Group < b->Group ? -1 : 1;
    return (a->Po < b->Po) - (a->Po > b->Po);
}
// The compact bank stores one DP representative per binding/area/profile.
// Expand only this live root's alternatives, preserving binding order and
// decreasing PO order within a binding. Each trial keeps its representative ID.
/**Function*************************************************************

  Synopsis    [Expand structural alternatives for one live union root.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmt_UnionExpand( Lmt_Union_t * u, int Root )
{
    Lmt_Man_t * p = u->p;
    Lmt_Alt_t * pAlts;
    int c, Po, i, Count, Group = 0, Prev = -1, Start = p->nCuts;
    Vec_IntClear(u->vExpand);
    for ( c = p->pHeads[Root]; c >= 0; c = Lmt_Next(p, c) )
    {
        if ( Prev >= 0 && Lmt_Owner(p, c) != Lmt_Owner(p, Prev) ) ++Group;
        Po = Lmt_Po(p, c);
        do
        {
            Vec_IntPush(u->vExpand, Group);
            Vec_IntPush(u->vExpand, c);
            Vec_IntPush(u->vExpand, Po);
        }
        while ( (Po = Abc_RecTargetNext3(Po)) >= 0 );
        Prev = c;
    }
    Count = Vec_IntSize(u->vExpand)/3;
    if ( !Count ) return 1;
    if ( (size_t)Start+Count > INT_MAX )
    { Abc_Print(-1, "LMS target: trial count exceeds addressable storage.\n"); return 0; }
    p->pExtras = (Lmt_Extra_t *)Lmt_Reserve(p, p->pExtras, &p->nExtraCap,
        (size_t)(Start-p->nBaseCuts)+Count, sizeof(Lmt_Extra_t));
    if ( p->fFailed ) return 0;
    pAlts = (Lmt_Alt_t *)Vec_IntArray(u->vExpand);
    qsort(pAlts, Count, sizeof(Lmt_Alt_t), Lmt_AltCompare);
    for ( i = 0; i < Count; ++i )
    {
        Lmt_Extra_t * pExtra = p->pExtras+Start-p->nBaseCuts+i;
        pExtra->Bind = Lmt_Owner(p, pAlts[i].Repr);
        pExtra->Po = pAlts[i].Po;
        pExtra->Repr = pAlts[i].Repr;
        pExtra->Next = i+1 < Count ? Start+i+1 : -1;
    }
    p->pHeads[Root] = Start;
    p->nCuts += Count;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Discard trial alternatives while preserving the selected winner.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Lmt_UnionCollapse( Lmt_Man_t * p, int Root, int Start, int Head )
{
    int Choice = p->pSelected[Root];
    p->pHeads[Root] = Head;
    p->nCuts = Start;
    if ( Choice >= Start )
    {
        Lmt_Extra_t Extra = p->pExtras[Choice-p->nBaseCuts];
        if ( Extra.Po == Lmt_Po(p, Extra.Repr) ) p->pSelected[Root] = Extra.Repr;
        else
        {
            // Persist only the winning structure. Leave the original profile
            // intact so restoring saved choices also restores their exact POs.
            Extra.Next = -1;
            p->pExtras[Start-p->nBaseCuts] = Extra;
            p->pSelected[Root] = p->nCuts++;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Recover area using a shared physical candidate graph.]

  Description [Keep deadline-DP coordination and explore all live logical
  roots in reverse order. Hash candidates lazily with their current leaf
  implementations. The union shares interiors across original gates and
  alternatives, including trial fanouts. Clean up once at the end.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Lmt_UnionRecover( Lmt_Man_t * p, Gia_Man_t * pBest, int fVerbose )
{
    Lmt_Union_t Union, * u = &Union;
    Gia_Obj_t * pObj;
    Gia_Man_t * pClean;
    Lmt_Rank_t * pRank = p->Exact ? ABC_ALLOC(Lmt_Rank_t, p->Exact) : NULL;
    int Id, c, n = Gia_ManObjNum(p->pGia), Before = Gia_ManAndNum(pBest);
    int fGroups = p->nAlternatives > (size_t)p->nBaseCuts;
    int * pSavedChoices = ABC_ALLOC(int, n);
    abctime Start = Abc_Clock();
    memset(u, 0, sizeof(*u));
    memcpy(pSavedChoices, p->pSelected, sizeof(int)*n);
    u->p = p;
    u->vRefs = Vec_IntAlloc(n);
    u->vLevels = Vec_IntAlloc(n);
    u->vSeen = Vec_IntAlloc(n);
    u->vStack = Vec_IntAlloc(100);
    u->vReq = Vec_IntAlloc(n);
    u->vLive = Vec_IntAlloc(n);
    u->vDirty = Vec_IntAlloc(100);
    u->vSaved = Vec_IntAlloc(100);
    u->vRefresh = Vec_IntAlloc(100);
    u->vExpand = fGroups ? Vec_IntAlloc(100) : NULL;
    u->vGroupLevels = fGroups ? Vec_IntAlloc(100) : NULL;
    u->vProbeMark = Vec_IntAlloc(n);
    u->vVirt = Vec_IntAlloc(100);
    u->vVirtMark = Vec_IntAlloc(100);
    u->vProbeStack = Vec_IntAlloc(100);
    u->DirtyRoot = -1;
    u->vFanouts = Vec_WecStart(n);
    u->pLits = ABC_CALLOC(int, n);
    u->pMarks = ABC_CALLOC(int, n);
    u->pChanged = ABC_CALLOC(int, n);
    u->pFresh = ABC_CALLOC(int, n);
    for ( Id = 0; Id < n; ++Id )
    {
        if ( p->pRequired[Id] == ABC_INFINITY ) p->pSelected[Id] = -1;
        p->pRefs[Id] = 0;
    }
    Gia_ManForEachCo(p->pGia, pObj, Id) Lmt_RefNode(p, Gia_ObjFaninId0p(p->pGia, pObj), 1);
    Lmt_UnionSeed(u);
    assert(u->Area == Before);
#ifdef LMS_TARGET_CHECK_UNION
    Lmt_UnionCheck(u);
#endif
    Gia_ManForEachObj(p->pGia, pObj, Id)
    {
        if ( Gia_ObjIsAnd(pObj) || Gia_ObjIsCo(pObj) )
            Lmt_UnionFanouts(u, Id, p->pSelected[Id], 1);
    }
    for ( Id = n-1; Id > 0; --Id )
    {
        int Start, Head;
        if ( !p->pRefs[Id] || !Gia_ObjIsAnd(Gia_ManObj(p->pGia, Id)) ||
            !Vec_IntEntry(u->vRefs, Abc_Lit2Var(u->pLits[Id])) ) continue;
        Lmt_UnionTry(u, Id, -1);
        Start = p->nCuts;
        Head = p->pHeads[Id];
        // With one structure per profile, the base chain already has the
        // full trial order. Avoid sorting and copying it into extras.
        if ( fGroups && !Lmt_UnionExpand(u, Id) ) break;
        if ( p->Exact ) Lmt_UnionRank(u, Id, pRank);
        else for ( c = p->pHeads[Id]; c >= 0; c = Lmt_Next(p, c) ) Lmt_UnionTry(u, Id, c);
        if ( fGroups ) Lmt_UnionCollapse(p, Id, Start, Head);
    }
    Gia_ManForEachCo(p->pGia, pObj, Id) Gia_ManAppendCo(u->pGraph, u->pLits[Gia_ObjId(p->pGia, pObj)]);
    Gia_ManHashStop(u->pGraph);
    pClean = Gia_ManCleanup(u->pGraph);
    assert(Gia_ManAndNum(pClean) == u->Area);
    if ( Gia_ManAndNum(pClean) <= Before && Lmt_CheckTiming(p, pClean) )
    {
        pClean->pName = Abc_UtilStrsav(p->pGia->pName);
        pClean->pSpec = Abc_UtilStrsav(p->pGia->pSpec);
        if ( p->pGia->vNamesIn ) pClean->vNamesIn = Vec_PtrDupStr(p->pGia->vNamesIn);
        if ( p->pGia->vNamesOut ) pClean->vNamesOut = Vec_PtrDupStr(p->pGia->vNamesOut);
        Gia_ManStop(pBest); pBest = pClean;
    }
    else
    {
        Abc_Print(-1, "LMS target: union recovery failed validation; keeping its input.\n");
        Gia_ManStop(pClean); memcpy(p->pSelected, pSavedChoices, sizeof(int)*n); Lmt_Reach(p);
    }
    if ( fVerbose ) Abc_Print(1, "LMS target union: %d -> %d ANDs; %d changes; %.0f bindings, %.0f exact trials, %.0f affected nodes; %d rebases; %.3f s.\n",
        Before, Gia_ManAndNum(pBest), u->nChanges, u->nCandidates, u->nTrials, u->nTouched, u->nRebases,
        (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
    if ( fVerbose && p->Exact ) Abc_Print(1, "LMS target union filters: %.0f predicted-late candidates and %.0f nonnegative probes skipped (heuristic shortlist).\n",
        u->nLate, u->nNonnegative);
    if ( fVerbose ) Abc_Print(1, "LMS target union profiles: %.0f level checks; %.0f current-structure trials skipped.\n",
        u->nProfiles, u->nCurrent);
    Gia_ManStop(u->pGraph);
    Vec_IntFree(u->vRefs); Vec_IntFree(u->vLevels); Vec_IntFree(u->vSeen); Vec_IntFree(u->vStack);
    Vec_IntFree(u->vDirty); Vec_IntFree(u->vSaved); Vec_WecFree(u->vFanouts);
    Vec_IntFree(u->vRefresh);
    Vec_IntFreeP(&u->vExpand);
    Vec_IntFreeP(&u->vGroupLevels);
    Vec_IntFree(u->vProbeMark); Vec_IntFree(u->vVirt); Vec_IntFree(u->vVirtMark); Vec_IntFree(u->vProbeStack);
    Vec_IntFree(u->vReq); Vec_IntFree(u->vLive); ABC_FREE(pRank);
    ABC_FREE(u->pLits); ABC_FREE(u->pMarks); ABC_FREE(u->pChanged);
    ABC_FREE(u->pFresh);
    ABC_FREE(pSavedChoices);
    return pBest;
}

/**Function*************************************************************

  Synopsis    [Collect a retained cut and stop on a candidate-bank failure.]

  Description []

  SideEffects [Adds library alternatives to the bank.]

  SeeAlso     []

***********************************************************************/
static int Lmt_CollectCut( void * pData, int Root, int n, const int * pLeaves, word Truth, const Lms_CutMatch_t * pMatch )
{
    Abc_RecTargetCollect3(pData, Root, n, pLeaves, Truth, pMatch);
    return !((Lmt_Man_t *)pData)->fFailed;
}

/**Function*************************************************************

  Synopsis    [Keep every choice member's direct gate as a library-free fallback.]

  Description [Choice links have already been checked by the collector.
  Only roots with ordinary consumers need a bank. Member fanins precede
  the representative, so the existing DP and reconstruction order applies.]

  SideEffects [Adds explicit one-AND candidates with relative output phase.]

  SeeAlso     []

***********************************************************************/
static void Lmt_ChoiceGates( Lmt_Man_t * p )
{
    static const int AndPo = -2;
    Gia_Obj_t * pObj, * pMember;
    int Id, Member, Leaves[2];
    Gia_ManForEachAnd(p->pGia, pObj, Id)
    {
        if ( !p->pRefs[Id] ) continue;
        for ( Member = Gia_ObjSibl(p->pGia, Id); Member; Member = Gia_ObjSibl(p->pGia, Member) )
        {
            pMember = Gia_ManObj(p->pGia, Member);
            Leaves[0] = Gia_ObjFaninLit0p(p->pGia, pMember);
            Leaves[1] = Gia_ObjFaninLit1p(p->pGia, pMember);
            Lms_TargetCut(p, Id, 2, Leaves, Gia_ObjPhase(pObj) ^ Gia_ObjPhase(pMember), &AndPo, 1);
            if ( p->fFailed ) return;
        }
    }
}

/**Function*************************************************************

  Synopsis    [Copy the output-reachable implementation without choices.]

  Description [Unused choice alternatives are not part of the baseline area.
  Reverse marking and forward copying avoid recursion even on deep AIGs.]

  SideEffects [Uses scratch Values on the input.]

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Lmt_ChoiceBaseline( Gia_Man_t * pGia )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    unsigned char * pUsed = ABC_CALLOC(unsigned char, Gia_ManObjNum(pGia));
    int Id;
    if ( !pUsed ) return NULL;
    Gia_ManForEachCo(pGia, pObj, Id) pUsed[Gia_ObjFaninId0p(pGia, pObj)] = 1;
    for ( Id = Gia_ManObjNum(pGia)-1; Id > 0; --Id )
    {
        pObj = Gia_ManObj(pGia, Id);
        if ( !pUsed[Id] || !Gia_ObjIsAnd(pObj) ) continue;
        pUsed[Gia_ObjFaninId0p(pGia, pObj)] = 1;
        pUsed[Gia_ObjFaninId1p(pGia, pObj)] = 1;
    }
    pNew = Gia_ManStart(Gia_ManObjNum(pGia));
    pNew->pName = Abc_UtilStrsav(pGia->pName);
    pNew->pSpec = Abc_UtilStrsav(pGia->pSpec);
    pNew->fGiaSimple = pGia->fGiaSimple;
    Gia_ManConst0(pGia)->Value = 0;
    Gia_ManForEachObj1(pGia, pObj, Id)
    {
        if ( Gia_ObjIsCi(pObj) ) pObj->Value = Gia_ManAppendCi(pNew);
        else if ( Gia_ObjIsCo(pObj) ) Gia_ManAppendCo(pNew, Gia_ObjFanin0Copy(pObj));
        else if ( pUsed[Id] ) pObj->Value = Gia_ManAppendAnd(pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj));
    }
    ABC_FREE(pUsed);
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Validate optional nonnegative integer timing constraints.]

  Description [ABC_INFINITY denotes an unconstrained output. Finite times
  must be smaller, so it remains distinct from an unvisited requirement.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmt_TimingValid( Gia_Man_t * pGia, int Target )
{
    int i, Time;
    if ( Target < -1 || Target >= ABC_INFINITY )
    { Abc_Print(-1, "LMS target: invalid global deadline.\n"); return 0; }
    if ( pGia->vCiArrs && Vec_IntSize(pGia->vCiArrs) != Gia_ManCiNum(pGia) )
    { Abc_Print(-1, "LMS target: arrival vector must have one entry per CI.\n"); return 0; }
    if ( pGia->vCoReqs && Vec_IntSize(pGia->vCoReqs) != Gia_ManCoNum(pGia) )
    { Abc_Print(-1, "LMS target: required vector must have one entry per CO.\n"); return 0; }
    if ( pGia->vCiArrs )
        Vec_IntForEachEntry(pGia->vCiArrs, Time, i)
            if ( Time < 0 || Time >= ABC_INFINITY )
            { Abc_Print(-1, "LMS target: CI %d arrival must be in [0, ABC_INFINITY).\n", i); return 0; }
    if ( pGia->vCoReqs )
        Vec_IntForEachEntry(pGia->vCoReqs, Time, i)
            if ( Time < 0 || Time > ABC_INFINITY )
            { Abc_Print(-1, "LMS target: CO %d requirement must be in [0, ABC_INFINITY].\n", i); return 0; }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Resolve per-output deadlines and the maximum DP deadline.]

  Description [Without output requirements, automatic mode uses the bank's
  earliest maximum arrival. Given requirements take its place. An explicit
  target caps every output, including otherwise unconstrained outputs.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Lmt_SetupTiming( Lmt_Man_t * p, int Target, int fVerbose )
{
    Gia_Obj_t * pObj;
    int i;
    if ( Target < 0 && !p->pGia->vCoReqs )
    {
        Target = 0;
        Gia_ManForEachCo(p->pGia, pObj, i)
            Target = Abc_MaxInt(Target, p->pMinArr[Gia_ObjFaninId0p(p->pGia, pObj)]);
        if ( Target >= ABC_INFINITY )
        { Abc_Print(-1, "LMS target: earliest output arrival exceeds the finite timing range.\n"); return 0; }
        if ( fVerbose ) Abc_Print(1, "LMS target: automatic %s %d from the cut bank.\n", p->pGia->vCiArrs ? "arrival" : "depth", Target);
    }
    p->pCoRequired = ABC_ALLOC(int, Gia_ManCoNum(p->pGia)+1);
    if ( !p->pCoRequired )
    { Abc_Print(-1, "LMS target: cannot allocate output deadlines.\n"); return 0; }
    p->Target = 0;
    Gia_ManForEachCo(p->pGia, pObj, i)
    {
        int Required = Target < 0 ? ABC_INFINITY-1 : Target;
        if ( p->pGia->vCoReqs ) Required = Abc_MinInt(Required, Vec_IntEntry(p->pGia->vCoReqs, i));
        p->pCoRequired[i] = Required;
        p->Target = Abc_MaxInt(p->Target, Required);
    }
    if ( fVerbose && p->pGia->vCoReqs )
        Abc_Print(1, "LMS target: using per-output requirements%s.\n", Target < 0 ? "" : " capped by the global deadline");
    return 1;
}

/**Function*************************************************************

  Synopsis    [Extend critical budgets through interiors of selected macros.]

  Description [Other live cover roots form the boundary. AND fanins and
  choice links point to earlier nodes, so one reverse pass marks interiors
  without recursion or repeatedly walking cones shared by critical roots.]

  SideEffects [Updates node budgets and returns the number of added nodes.]

  SeeAlso     [Lmt_AdaptiveCuts]

***********************************************************************/
static int Lmt_ExpandCriticalCuts( Lmt_Man_t * p, int * pLimits, int CriticalCuts )
{
    Gia_Obj_t * pObj;
    int Id, k, nAdded = 0;
    for ( Id = Gia_ManObjNum(p->pGia)-1; Id > 0; --Id )
    {
        int Fans[3];
        pObj = Gia_ManObj(p->pGia, Id);
        if ( pLimits[Id] != CriticalCuts || !Gia_ObjIsAnd(pObj) ) continue;
        Fans[0] = Gia_ObjFaninId0p(p->pGia, pObj);
        Fans[1] = Gia_ObjFaninId1p(p->pGia, pObj);
        Fans[2] = Gia_ObjSibl(p->pGia, Id);
        for ( k = 0; k < 3; ++k )
            if ( p->pRequired[Fans[k]] == ABC_INFINITY && pLimits[Fans[k]] != CriticalCuts &&
                 Gia_ObjIsAnd(Gia_ManObj(p->pGia, Fans[k])) )
            { pLimits[Fans[k]] = CriticalCuts; ++nAdded; }
    }
    return nAdded;
}

/**Function*************************************************************

  Synopsis    [Keep first-pass candidates ahead of newly collected cuts.]

  Description [New bindings were prepended during collection. Rotate each
  affected chain once, retaining its original first-pass and second-pass
  orders. Candidate IDs remain stable for profile and owner lookups.]

  SideEffects [Sets the first-bank tie boundary and relinks binding chains.]

  SeeAlso     [Lmt_GetCut]

***********************************************************************/
static void Lmt_OrderRecollected( Lmt_Man_t * p, int FirstCuts )
{
    int Id, Head, LastNew, FirstOld, LastOld;
    p->nFirstCuts = FirstCuts;
    p->nBaseCuts = p->nCuts;
    for ( Id = 0; Id < Gia_ManObjNum(p->pGia); ++Id )
    {
        Head = p->pHeads[Id];
        if ( Head < FirstCuts ) continue;
        LastNew = p->pOwners[Head];
        while ( p->pBinds[LastNew].Next >= FirstCuts )
            LastNew = p->pOwners[p->pBinds[LastNew].Next];
        FirstOld = p->pBinds[LastNew].Next;
        if ( FirstOld < 0 ) continue;
        LastOld = p->pOwners[FirstOld];
        while ( p->pBinds[LastOld].Next >= 0 )
            LastOld = p->pOwners[p->pBinds[LastOld].Next];
        p->pBinds[LastOld].Next = Head;
        p->pBinds[LastNew].Next = -1;
        p->pHeads[Id] = FirstOld;
    }
}

/**Function*************************************************************

  Synopsis    [Expand the bank at zero-slack macros of a pilot cover.]

  Description [Keep the first bank and append distinct cuts from a second
  collection, after the first candidates in tie order. Extend the larger
  budget through macro interiors; other cover roots retain their budgets.
  Skip duplicate visits outside the changed budgets' fanout. Rebuild deadline
  bounds only when candidates or pilot deadlines changed. Returns -1 on
  failure, 0 to reuse the pilot round, or 1 to restart selection.
  Pilot-only deadline relaxation never applies to the returned result.]

  SideEffects [Rebuilds derived tables when the bank grows.]

  SeeAlso     [Lms_TargetPerformAdaptive]

***********************************************************************/
static int Lmt_AdaptiveCuts( Lmt_Man_t * p, int Cuts, int CriticalCuts,
    int Target, int Memory, int fRelaxed, abctime * pCutTime, int fVerbose )
{
    int n = Gia_ManObjNum(p->pGia), Id, Result = -1, nCritical = 0, OldCuts = p->nCuts;
    int OldTarget = p->Target, nInternal;
    int * pLimits = ABC_ALLOC(int, n), * pLevels = ABC_CALLOC(int, n);
    Gia_Obj_t * pObj;
    size_t Slots;
    abctime Start = Abc_Clock(), CutStart;
    if ( !pLimits || !pLevels )
    { Abc_Print(-1, "LMS target: cannot allocate adaptive cut budgets.\n"); goto cleanup; }
    // Levels initializes output requirements for refinement; preserve the
    // completed pilot requirements while using its cover-level computation.
    memcpy(pLimits, p->pRequired, n*sizeof(int));
    Lmt_Levels(p, pLevels);
    memcpy(p->pRequired, pLimits, n*sizeof(int));
    Gia_ManForEachObj(p->pGia, pObj, Id)
    {
        int Required = p->pRequired[Id];
        pLimits[Id] = Cuts;
        if ( !Gia_ObjIsAnd(pObj) || Required == ABC_INFINITY ) continue;
        assert(pLevels[Id] <= Required);
        if ( pLevels[Id] == Required )
        { pLimits[Id] = CriticalCuts; ++nCritical; }
    }
    nInternal = Lmt_ExpandCriticalCuts(p, pLimits, CriticalCuts);
    if ( fVerbose )
        Abc_Print(1, "LMS adaptive cuts: %d critical roots and %d internal ANDs / %d at budget %d; other nodes at %d.\n",
            nCritical, nInternal, Gia_ManAndNum(p->pGia), CriticalCuts, Cuts);
    if ( nCritical )
    {
        CutStart = Abc_Clock();
        if ( !Lms_CutsRecollect(p->pGia, Cuts, pLimits, Abc_RecTargetCost3, Lmt_CollectCut, p, fVerbose) )
            goto cleanup;
        *pCutTime += Abc_Clock()-CutStart;
        if ( p->fFailed ) goto cleanup;
    }
    if ( p->nCuts == OldCuts && !fRelaxed )
    { Result = 0; goto cleanup; }
    if ( p->nCuts != OldCuts )
    {
        Lmt_OrderRecollected(p, OldCuts);
        Lmt_FreePrepare(p);
        if ( !Lmt_Prepare(p) ) goto cleanup;
    }
    ABC_FREE(p->pCoRequired);
    if ( !Lmt_SetupTiming(p, Target, fVerbose) ) goto cleanup;
    assert(p->Target <= OldTarget);
    // The deadline layout needs structural references, not pilot cover refs.
    memset(p->pRefs, 0, n*sizeof(int));
    Gia_ManForEachObj(p->pGia, pObj, Id)
    {
        if ( Gia_ObjIsAnd(pObj) || Gia_ObjIsCo(pObj) ) ++p->pRefs[Gia_ObjFaninId0p(p->pGia, pObj)];
        if ( Gia_ObjIsAnd(pObj) ) ++p->pRefs[Gia_ObjFaninId1p(p->pGia, pObj)];
        p->pSelected[Id] = -1;
    }
    if ( !Lmt_DeadlineLayout(p, Memory) ) goto cleanup;
    Slots = p->pOffsets[n];
    ABC_FREE(p->pCost); ABC_FREE(p->pChoice);
    p->pCost = ABC_CALLOC(float, Slots);
    p->pChoice = ABC_ALLOC(int, Slots);
    if ( !p->pCost || !p->pChoice )
    { Abc_Print(-1, "LMS target: cannot allocate the expanded deadline table.\n"); goto cleanup; }
    Result = 1;
cleanup:
    if ( fVerbose && Result >= 0 )
        Abc_Print(1, "LMS adaptive cuts: %d new profiles; %.3f s%s.\n",
            p->nCuts-OldCuts, (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC,
            Result ? "" : "; reusing the pilot round");
    ABC_FREE(pLimits); ABC_FREE(pLevels);
    return Result;
}

/**Function*************************************************************

  Synopsis    [Optimize area under a depth target using direct GIA cuts.]

  Description [Unit AND delays, optional integer CI arrivals and CO requirements,
  fixed six-input library. Target -1 uses the given output requirements or,
  without them, the earliest maximum arrival in the collected candidate bank.
  Memory bounds the deadline table in MiB; zero retains all distinct states.
  Selection is an area-flow heuristic, not an exact minimum. Each round
  revises sharing estimates from the selected cover and retains the best
  actual feasible AIG. CriticalCuts above Cuts enables a pilot cover and
  a larger cut budget at its zero-slack roots and macro interiors before
  the normal rounds. First-pass candidates win ties against new cuts.
  Failure returns NULL and leaves the input intact.]

  SideEffects [Uses scratch levels and Values on the input.]

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Lms_TargetPerformAdaptive( Gia_Man_t * pGia, int Target, int Cuts, int Rounds, int Exact, int DpMode, int Memory, int CriticalCuts, int fVerbose )
{
    Lmt_Man_t Man, * p = &Man;
    Gia_Man_t * pBest = NULL, * pNew, * pBaseline = NULL;
    Gia_Obj_t * pObj;
    int Id, r, Count, BestCount = 0, OriginalLevel, OriginalCount = Gia_ManAndNum(pGia);
    int fLazy = DpMode != 0, nObjs = Gia_ManObjNum(pGia);
    int fProbeDense = 0, fRecollected = CriticalCuts <= Cuts, fPilotRelaxed = 0, InputTarget = Target;
    int * pBestSelected = NULL, * pBestRequired = NULL;
    size_t Slots = 0;
    abctime Start = Abc_Clock(), CutTime, LazyTime = 0;
    memset(p, 0, sizeof(*p));
    p->pGia = pGia;
    p->Target = Target;
    p->Exact = Exact;
    if ( !Abc_RecTargetReady3() || pGia->pManTime
        || pGia->pMuxes || Gia_ManXorNum(pGia) || Gia_ManBufNum(pGia) || Gia_ManRegNum(pGia) || Gia_ManConstrNum(pGia) )
    {
        Abc_Print(-1, "LMS target: requires a combinational AIG and a six-input AND-cost structure library (no boxes or buffers).\n");
        return NULL;
    }
    if ( !Lmt_TimingValid(pGia, Target) ) return NULL;
    if ( CriticalCuts < 0 || CriticalCuts > 128 )
    { Abc_Print(-1, "LMS target: critical cut budget must be in [0, 128].\n"); return NULL; }
    if ( Gia_ManHasChoices(pGia) )
    {
        // Cut imports and direct member gates use the same relative phase.
        Gia_ManSetPhase(pGia);
        pBaseline = Lmt_ChoiceBaseline(pGia);
        if ( !pBaseline )
        { Abc_Print(-1, "LMS target: cannot allocate the choice-free baseline.\n"); return NULL; }
        OriginalCount = Gia_ManAndNum(pBaseline);
        if ( fVerbose ) Abc_Print(1, "LMS target choices: %d stored ANDs, %d in the output-reachable baseline.\n", Gia_ManAndNum(pGia), OriginalCount);
    }
    OriginalLevel = Gia_ManLevelNum(pBaseline ? pBaseline : pGia);
    p->vPrograms = Vec_IntAlloc(1000);
    p->vProgramOffsets = Vec_IntAlloc(1000);
    p->vLabels = Vec_IntAlloc(100);
    p->vRefStack = Vec_IntAlloc(100);
    p->pHeads = ABC_ALLOC(int, nObjs);
    for ( Id = 0; Id < nObjs; ++Id ) p->pHeads[Id] = -1;
    p->pRefs = ABC_CALLOC(int, nObjs);
    if ( !p->pRefs )
    { Abc_Print(-1, "LMS target: cannot allocate reference counts.\n"); goto cleanup; }
    Gia_ManForEachObj(pGia, pObj, Id)
    {
        if ( Gia_ObjIsAnd(pObj) || Gia_ObjIsCo(pObj) ) ++p->pRefs[Gia_ObjFaninId0p(pGia, pObj)];
        if ( Gia_ObjIsAnd(pObj) ) ++p->pRefs[Gia_ObjFaninId1p(pGia, pObj)];
    }
    Abc_RecTargetCache3(1);
    if ( !Lms_CutsCollect(pGia, Cuts, Abc_RecTargetCost3, Lmt_CollectCut, p, fVerbose) ) goto cleanup;
    if ( Gia_ManHasChoices(pGia) ) Lmt_ChoiceGates(p);
    CutTime = Abc_Clock();
    if ( p->fFailed ) goto cleanup;
    p->nBaseCuts = p->nCuts;
    if ( !Lmt_Profiles(p) ) goto cleanup;
    if ( fVerbose ) Abc_Print(1, "LMS target profiles: %d bindings, %d representatives retain %zu structural alternatives.\n", p->nBinds, p->nBaseCuts, p->nAlternatives);
    p->pOffsets = ABC_ALLOC(size_t, (size_t)nObjs+1);
    if ( !p->pOffsets )
    { Abc_Print(-1, "LMS target: cannot allocate deadline offsets.\n"); goto cleanup; }
    if ( !Lmt_Prepare(p) ) goto cleanup;
    if ( Lmt_BankBytes(p) > LMS_TARGET_MEMORY_NOTE )
        Abc_Print(0, "LMS target: candidate tables use %.2f MiB; continuing.\n", Lmt_BankBytes(p)/(1024*1024));
    if ( !Lmt_SetupTiming(p, Target, fVerbose) ) goto cleanup;
    if ( !fRecollected )
        Gia_ManForEachCo(pGia, pObj, Id)
        {
            int Arrival = p->pMinArr[Gia_ObjFaninId0p(pGia, pObj)];
            // An initially infeasible request can become feasible after
            // expansion. Relax only the pilot; restore every requested
            // output deadline before constructing a result.
            if ( Arrival < ABC_INFINITY && p->pCoRequired[Id] < Arrival )
            { p->pCoRequired[Id] = Arrival; fPilotRelaxed = 1; }
            p->Target = Abc_MaxInt(p->Target, p->pCoRequired[Id]);
        }
    if ( fVerbose && fPilotRelaxed )
        Abc_Print(1, "LMS adaptive cuts: relaxing infeasible deadlines for the pilot only.\n");
    Target = p->Target;
    if ( !Lmt_DeadlineLayout(p, Memory) ) goto cleanup;
    Slots = p->pOffsets[nObjs];
    p->pCost = ABC_CALLOC(float, Slots);
    p->pChoice = ABC_ALLOC(int, Slots);
    if ( !p->pCost || !p->pChoice )
    { Abc_Print(-1, "LMS target: cannot allocate %.2f MiB for the deadline table.\n", (double)Slots*(sizeof(float)+sizeof(int))/(1024*1024)); goto cleanup; }
    p->pRequired = ABC_ALLOC(int, nObjs);
    p->pSelected = ABC_ALLOC(int, nObjs);
    pBestSelected = ABC_ALLOC(int, nObjs);
    pBestRequired = ABC_ALLOC(int, nObjs);
    for ( Id = 0; Id < nObjs; ++Id ) p->pSelected[Id] = -1;
    p->pWeights = ABC_ALLOC(float, nObjs);
    for ( Id = 0; Id < nObjs; ++Id ) p->pWeights[Id] = (float)Abc_MaxInt(1, p->pRefs[Id]);
    for ( r = 0; r < Rounds; ++r )
    {
        abctime DpStart = Abc_ThreadClock(), DpTime;
        Lmt_Bounds(p);
        Lmt_Compute(p, fLazy);
        Count = Lmt_Select(p);
        DpTime = Abc_ThreadClock()-DpStart;
        if ( fVerbose ) Abc_Print(1, "LMS target DP: %s, %zu evaluations / %zu slots, %.3f s%s.\n",
            fLazy ? "lazy" : "dense", p->nVisited, p->nStates,
            (double)DpTime/CLOCKS_PER_SEC, p->fDenseFallback ? ", depth fallback" : "");
        if ( !fRecollected && Count >= 0 )
        {
            int Status = Lmt_AdaptiveCuts(p, Cuts, CriticalCuts, InputTarget, Memory,
                fPilotRelaxed, &CutTime, fVerbose);
            if ( Status < 0 ) goto cleanup;
            fRecollected = 1;
            Target = p->Target;
            Slots = p->pOffsets[nObjs];
            if ( Status > 0 ) { r = -1; continue; }
        }
        // Reuse existing rounds as timing probes, not extra optimization
        // passes. State coverage alone does not predict memoization cost.
        // Thread time limits scheduling noise; timing affects only traversal,
        // never the recurrence, tie-breaks, or number of optimization rounds.
        if ( p->fDenseFallback ) { fLazy = 0; fProbeDense = 0; }
        else if ( DpMode == 2 && fProbeDense )
        { fLazy = LazyTime <= DpTime; fProbeDense = 0; }
        else if ( DpMode == 2 && r == 0 && p->nVisited > p->nStates/2 && Rounds > 2 )
        { LazyTime = DpTime; fLazy = 0; fProbeDense = 1; }
        if ( Count < 0 )
        { Abc_Print(-1, "LMS target: target %d%s not reached by retained cuts; input unchanged.\n", Target, pGia->vCoReqs ? " / output requirements" : ""); break; }
        pNew = Lmt_Build(p);
        if ( fVerbose )
            Abc_Print(1, "LMS target round %d: %d replacements, %d ANDs, depth %d.\n",
                r+1, Count, Gia_ManAndNum(pNew), Gia_ManLevelNum(pNew));
        if ( Lmt_CheckTiming(p, pNew) && (!pBest || Gia_ManAndNum(pNew) < Gia_ManAndNum(pBest)) )
        {
            if ( pBest ) Gia_ManStop(pBest);
            pBest = pNew;
            BestCount = Count;
            memcpy(pBestSelected, p->pSelected, sizeof(int)*nObjs);
            memcpy(pBestRequired, p->pRequired, sizeof(int)*nObjs);
        }
        else Gia_ManStop(pNew);
        for ( Id = 0; Id < nObjs; ++Id )
            p->pWeights[Id] = 0.5f * (p->pWeights[Id] + (float)Abc_MaxInt(1, p->pRefs[Id]));
    }
    if ( pBest )
    {
        memcpy(p->pSelected, pBestSelected, sizeof(int)*nObjs);
        memcpy(p->pRequired, pBestRequired, sizeof(int)*nObjs);
        pBest = Lmt_Refine(p, pBest, fVerbose);
        pBest = Lmt_UnionRecover(p, pBest, fVerbose);
        BestCount = Lmt_Reach(p);
        if ( Gia_ManAndNum(pBest) >= OriginalCount && Lmt_CheckTiming(p, pBaseline ? pBaseline : pGia) )
        {
            Gia_ManStop(pBest);
            pBest = pBaseline ? pBaseline : Gia_ManDup(pGia);
            pBaseline = NULL;
            BestCount = 0;
        }
        if ( pGia->vCiArrs || pGia->vCoReqs )
        {
            Vec_Int_t * vBefore = Lmt_CoArrivals(p, pBaseline ? pBaseline : pGia);
            Vec_IntFreeP(&pBest->vCiArrs);
            Vec_IntFreeP(&pBest->vCoReqs);
            Vec_IntFreeP(&pBest->vCoArrs);
            if ( pGia->vCiArrs ) pBest->vCiArrs = Vec_IntSize(pGia->vCiArrs) ? Vec_IntDup(pGia->vCiArrs) : Vec_IntAlloc(0);
            if ( pGia->vCoReqs ) pBest->vCoReqs = Vec_IntSize(pGia->vCoReqs) ? Vec_IntDup(pGia->vCoReqs) : Vec_IntAlloc(0);
            pBest->vCoArrs = Lmt_CoArrivals(p, pBest);
            Abc_Print(1, "LMS timing: maximum output arrival %d -> %d; all output deadlines met.\n",
                Vec_IntSize(vBefore) ? Vec_IntFindMax(vBefore) : 0,
                Vec_IntSize(pBest->vCoArrs) ? Vec_IntFindMax(pBest->vCoArrs) : 0);
            Vec_IntFree(vBefore);
        }
        if ( fVerbose ) Abc_Print(1, "LMS target bank: %d unique candidates, %u duplicates removed; candidate tables %.2f MiB, deadline table %.2f MiB.\n",
            p->nBaseCuts, p->nDuplicates, Lmt_BankBytes(p)/(1024*1024),
            (double)Slots*(sizeof(float)+sizeof(int))/(1024*1024));
        Abc_Print(1, "LMS target: %d -> %d ANDs; depth %d -> %d (target %d); %d replacements; %d candidates. Cuts %.3f s; total %.3f s.\n",
            OriginalCount, Gia_ManAndNum(pBest), OriginalLevel, Gia_ManLevelNum(pBest), Target,
            BestCount, p->nBaseCuts, (double)(CutTime-Start)/CLOCKS_PER_SEC, (double)(Abc_Clock()-Start)/CLOCKS_PER_SEC);
    }
cleanup:
    if ( pBaseline ) Gia_ManStop(pBaseline);
    Abc_RecTargetCache3(0);
    Vec_IntFree(p->vPrograms); Vec_IntFree(p->vProgramOffsets); Vec_IntFree(p->vLabels);
    Vec_IntFree(p->vRefStack);
    Vec_IntFreeP(&p->vTiming);
    ABC_FREE(pBestSelected);
    ABC_FREE(pBestRequired);
    ABC_FREE(p->pBinds); ABC_FREE(p->pOwners);
    ABC_FREE(p->pProfiles); ABC_FREE(p->pExtras);
    ABC_FREE(p->pHash);
    ABC_FREE(p->pHeads);
    ABC_FREE(p->pOffsets);
    ABC_FREE(p->pCost);
    ABC_FREE(p->pChoice);
    ABC_FREE(p->pRequired);
    ABC_FREE(p->pCoRequired);
    ABC_FREE(p->pSelected);
    ABC_FREE(p->pRefs);
    ABC_FREE(p->pWeights);
    Lmt_FreePrepare(p);
    return pBest;
}

/**Function*************************************************************

  Synopsis    [Optimize using a single uniformly collected candidate bank.]

  Description [Preserve the default API without adaptive recollection.]

  SideEffects []

  SeeAlso     [Lms_TargetPerformAdaptive]

***********************************************************************/
Gia_Man_t * Lms_TargetPerform( Gia_Man_t * pGia, int Target, int Cuts,
    int Rounds, int Exact, int DpMode, int Memory, int fVerbose )
{
    return Lms_TargetPerformAdaptive(pGia, Target, Cuts, Rounds, Exact, DpMode, Memory, 0, fVerbose);
}

ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
