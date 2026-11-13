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
    CCaDiCaL *     pSat;
    Vec_Ptr_t *   vMaps;
    Vec_Int_t *   vVars;
    Vec_Int_t *   vCopies;
    Vec_Int_t *   vCiMap;
    Vec_Int_t *   vRoots;
    Vec_Int_t *   vStack;
    Vec_Wrd_t *   vWork;
    Vec_Int_t *   vMapIds;
    abctime       Start;
    abctime       Deadline;
    int           nVars;
    int           fStopped;
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

  Synopsis    [Allocates private unrolling and incremental solver state.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Bmc3G_Man_t * Bmc3G_Start( Gia_Man_t * pGia, Bmc_GiaPar_t * pPars )
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
    p->pFrames = Gia_ManStart( Gia_ManObjNum(p->pGia) );
    Gia_ManHashStart( p->pFrames );
    p->vMaps = Vec_PtrAlloc( 128 );
    p->vVars = Vec_IntAlloc( 1024 );
    p->vCopies = Vec_IntAlloc( 1024 );
    p->vCiMap = Vec_IntAlloc( 1024 );
    p->vRoots = Vec_IntAlloc( Gia_ManPoNum(pGia) );
    p->vStack = Vec_IntAlloc( 1024 );
    p->vWork = Vec_WrdAlloc( 1024 );
    Bmc3G_IndexCone( p );
    if ( p->fStopped ) return p;
    p->pSat = ccadical_init();
    ccadical_set_option( p->pSat, "quiet", 1 );
    // Avoid repeated elimination while adding circuit clauses incrementally.
    ccadical_set_option( p->pSat, "inprocessing", 0 );
    ccadical_set_option( p->pSat, "fastelim", 0 );
    // Whole-formula phase guesses are costly for short incremental queries.
    ccadical_set_option( p->pSat, "lucky", 0 );
    ccadical_set_option( p->pSat, "phase", pPars->fPhase );
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
            Var = Vec_IntEntry( p->vVars, Gia_ObjId(p->pFrames, pObj) );
            if ( Var <= 0 || ccadical_val(p->pSat, Var) <= 0 ) continue;
            Pi = Vec_IntEntry( p->vCiMap, 2*i );
            f = Vec_IntEntry( p->vCiMap, 2*i + 1 );
            assert( f <= Frame );
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
         pPars->nMemoryLimit < 0 || pPars->nMemoryLimit > (1 << 20) ||
         (pPars->fPhase != 0 && pPars->fPhase != 1) ||
         pPars->nLutSize < 3 || pPars->nLutSize > 8 || Gia_ManConstrNum(pGia) ||
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

  Synopsis    [Runs incremental GIA BMC using one CaDiCaL instance.]

  Description [Returns 0 with a verified counterexample, 1 for a complete
  safety proof, -1 for undecided, and -2 for unsupported input. Completing
  a finite frame limit is not a proof. Complete exploration through the
  finite-state bound is sufficient for small state spaces. No global frame,
  mutable static state, or helper thread is used.]

  SideEffects [Replaces pGia->pCexSeq and updates the caller's statistics.]

  SeeAlso     []

***********************************************************************/
int Bmc_GiaPerform( Gia_Man_t * pGia, Bmc_GiaPar_t * pPars )
{
    Bmc3G_Man_t * p;
    Gia_Obj_t * pObj;
    Abc_Cex_t * pCex = NULL;
    abctime clk, Start;
    int Frame, i, Lit, Root, Status, Result = -1, fTrivial = 1;
    if ( !Bmc3G_CheckInput(pGia, pPars) ) return -2;
    if ( pPars->pShared && !pPars->pShared->pFuncFrames ) return -2;
    pPars->nFramesDone = pPars->nFramesShared = pPars->nQueries = 0;
    pPars->fMemoryLimit = 0;
    pPars->iFrame = -1;
    pPars->timeUnroll = pPars->timeCnf = pPars->timeSat = 0;
    pPars->timeTeardown = pPars->timeSatOverrun = 0;
    pPars->MemoryPeakMB = 0;
    Abc_CexFreeP( &pGia->pCexSeq );
    p = Bmc3G_Start( pGia, pPars );
    if ( p->fStopped ) goto finish;
    Gia_ManForEachPo( p->pGia, pObj, i )
        fTrivial &= Gia_ObjFaninLit0p(p->pGia, pObj) == 0;
    if ( fTrivial ) { Result = 1; goto finish; }
    for ( Frame = 0; Frame < INT_MAX - 1 && (!pPars->nFramesMax || Frame < pPars->nFramesMax); Frame++ )
    {
        int fFrameTrivial = 1;
        if ( Bmc3G_Stop(p) ) break;
        clk = Abc_Clock();
        if ( !Bmc3G_MapStart(p) ) break;
        if ( pPars->pShared && pPars->pShared->pFuncFrames(pPars->pShared->pData, 0) > Frame )
        {
            pPars->nFramesShared++;
            pPars->timeUnroll += Abc_Clock() - clk;
            goto frame_done;
        }
        if ( !pPars->nQueries ) Bmc3G_PropagateConstants(p, Frame);
        Vec_IntClear( p->vRoots );
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
        clk = Abc_Clock();
        if ( !fFrameTrivial && !Bmc3G_AddCnf(p) )
        {
            pPars->timeCnf += Abc_Clock() - clk;
            break;
        }
        pPars->timeCnf += Abc_Clock() - clk;
        Vec_IntForEachEntry( p->vRoots, Root, i )
        {
            pObj = Gia_ManObj( p->pFrames, Root );
            if ( Gia_ObjFaninLit0p(p->pFrames, pObj) == 0 ) continue;
            if ( Bmc3G_Stop(p) ) break;
            Lit = Vec_IntEntry( p->vVars, Root );
            assert( Lit > 0 );
            clk = Abc_Clock();
            if ( pPars->nConfLimit ) ccadical_limit( p->pSat, "conflicts", pPars->nConfLimit );
            ccadical_assume( p->pSat, Lit );
            pPars->nQueries++;
            Status = ccadical_solve( p->pSat );
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
            break;
        }
        if ( i < Vec_IntSize(p->vRoots) ) break;
        if ( pPars->pShared ) pPars->pShared->pFuncFrames( pPars->pShared->pData, Frame + 1 );
frame_done:
        pPars->nFramesDone = Frame + 1;
        if ( pPars->fVerbose )
            Abc_Print( 1, "%4d + : Var = %d. Cla = %llu. Conf = %d. Time = %.3f sec\n",
                Frame, p->nVars, (unsigned long long)ccadical_live_clauses(p->pSat), ccadical_conflicts(p->pSat),
                (double)(Abc_Clock() - p->Start) / CLOCKS_PER_SEC );
        if ( Gia_ManRegNum(p->pGia) < 30 && Frame + 1 >= (1 << Gia_ManRegNum(p->pGia)) )
        {
            Result = 1;
            break;
        }
    }
finish:
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

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
