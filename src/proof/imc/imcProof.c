/**CFile****************************************************************

  FileName    [imcProof.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Interpolation-based model checking.]

  Synopsis    [McMillan interpolants from resolution and LRAT proofs.]

  Author      [ABC contributors]

  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - October 23, 2026.]

  Revision    [$Id: imcProof.c,v 1.00 2026/10/23 00:00:00 alanmi Exp $]

***********************************************************************/

// Keep proof positions wide on both Windows and 32-bit POSIX builds.
#ifndef _WIN32
#ifndef _FILE_OFFSET_BITS
#define _FILE_OFFSET_BITS 64
#endif
#ifndef _POSIX_C_SOURCE
#define _POSIX_C_SOURCE 200112L
#endif
#ifndef _DEFAULT_SOURCE
#define _DEFAULT_SOURCE 1
#endif
#ifndef _DARWIN_C_SOURCE
#define _DARWIN_C_SOURCE 1
#endif
#endif

#include "imcInt.h"
#include <limits.h>
#include "misc/mem/mem.h"
#ifdef _WIN32
#include <windows.h>
#include <io.h>
#include <fcntl.h>
#endif

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Imc_Cls_t_ Imc_Cls_t;
struct Imc_Cls_t_
{
    int iInter;            // partial interpolant, a GIA literal
    int nLits;
    int fPartA;            // original clause partition; -1 for derived clauses
    int nHints;            // LRAT antecedents stored after the literals
    int fUsed;             // reachable from the empty clause
    int pLits[0];
};

struct Imc_Prf_t_
{
    Gia_Man_t * pGia;
    Mem_Flex_t * pRootsMem, * pDerivedMem;
    Vec_Int_t * vSteps;     // recorded resolution pivots for every labeling
    Vec_Ptr_t * vClauses;   // original and derived clauses, indexed by LRAT ID
    Vec_Ptr_t * vPending;   // original clauses awaiting their LIDRUP IDs
    Vec_Int_t * vGlobal;    // SAT variable to interpolant input
    Vec_Int_t * vPartA;     // variables local to A
    Vec_Str_t * vVarSet;    // partition frozen by declaration or first use
    Vec_Int_t * vTrail;     // RUP assignments, including negated target clause
    Vec_Int_t * vSeen;      // marks to clear after resolution
    int nRoots;
    int fDual;
    int fPudlak;
    int fIncremental;
    int fMinimized;
    int fRead;              // nonincremental reader has been used
    int fFailed;            // incomplete incremental stream cannot be resumed
    ABC_INT64_T ProofOffset;
    int * pValues;
    int * pReasons;
    unsigned char * pSeen;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

// Windows tmpfile() may target a drive root without write permission.
// Delete-on-close keeps the stream private to this solver on both systems.
/**Function*************************************************************

  Synopsis    [Opens a temporary binary proof stream with portable cleanup.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
FILE * Imc_ProofFile( void )
{
#ifdef _WIN32
    char Path[MAX_PATH + 1], Name[MAX_PATH + 1];
    DWORD Length = GetTempPathA( MAX_PATH + 1, Path );
    int Fd;
    FILE * pFile;
    if ( !Length || Length > MAX_PATH || !GetTempFileNameA(Path, "imc", 0, Name) )
        return NULL;
    Fd = _open( Name, _O_RDWR | _O_BINARY | _O_TEMPORARY );
    if ( Fd < 0 )
    {
        DeleteFileA( Name );
        return NULL;
    }
    pFile = _fdopen( Fd, "w+b" );
    if ( pFile == NULL )
        _close( Fd );
    return pFile;
#else
    return tmpfile();
#endif
}

/**Function*************************************************************

  Synopsis    [Seeks within a proof stream without narrowing its byte offset.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Imc_ProofSeek( FILE * pFile, ABC_INT64_T Offset, int Origin )
{
#ifdef _WIN32
    return _fseeki64( pFile, Offset, Origin );
#else
    return fseeko( pFile, (off_t)Offset, Origin );
#endif
}

/**Function*************************************************************

  Synopsis    [Returns the full-width position of a proof stream.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
ABC_INT64_T Imc_ProofTell( FILE * pFile )
{
#ifdef _WIN32
    return _ftelli64( pFile );
#else
    return (ABC_INT64_T)ftello( pFile );
#endif
}

/**Function*************************************************************

  Synopsis    [Allocates a proof reader and initializes its interpolation partitions.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Imc_Prf_t * Imc_PrfStart( Vec_Int_t * vGlobals, int nVarsA, int nVars, int fDual, int fPudlak, int fIncremental )
{
    Imc_Prf_t * p = ABC_CALLOC( Imc_Prf_t, 1 );
    int i, Var;
    p->pRootsMem = Mem_FlexStart();
    p->pDerivedMem = Mem_FlexStart();
    p->vSteps = Vec_IntAlloc( 128 );
    p->fDual = fDual;
    p->fPudlak = fPudlak;
    p->fIncremental = fIncremental;
    p->pGia = Gia_ManStart( 1000 );
    p->pGia->fAddStrash = 1;
    Gia_ManHashStart( p->pGia );
    Vec_IntForEachEntry( vGlobals, Var, i )
        Gia_ManAppendCi( p->pGia );
    p->vClauses = Vec_PtrAlloc( 1000 );
    p->vPending = Vec_PtrAlloc( 16 );
    Vec_PtrPush( p->vClauses, NULL );
    p->vGlobal = Vec_IntInvert( vGlobals, -1 );
    p->vPartA = Vec_IntAlloc( nVars );
    p->vVarSet = Vec_StrStart( nVars );
    Vec_IntFill( p->vPartA, nVars, fDual );
    for ( i = 0; i < nVarsA; i++ )
    {
        Vec_IntWriteEntry( p->vPartA, i, !fDual );
        Vec_StrWriteEntry( p->vVarSet, i, 1 );
    }
    Vec_IntForEachEntry( vGlobals, Var, i )
        Vec_IntWriteEntry( p->vPartA, Var, 0 );
    p->vTrail = Vec_IntAlloc( 1000 );
    p->vSeen = Vec_IntAlloc( 1000 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Releases the proof reader, clause arenas, and interpolant network.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Imc_PrfStop( Imc_Prf_t * p )
{
    Mem_FlexStop( p->pRootsMem, 0 );
    Mem_FlexStop( p->pDerivedMem, 0 );
    Vec_IntFree( p->vSteps );
    Vec_PtrFree( p->vClauses );
    Vec_PtrFree( p->vPending );
    Vec_IntFree( p->vGlobal );
    Vec_IntFree( p->vPartA );
    Vec_StrFree( p->vVarSet );
    Vec_IntFree( p->vTrail );
    Vec_IntFree( p->vSeen );
    Gia_ManStopP( &p->pGia );
    ABC_FREE( p->pValues );
    ABC_FREE( p->pReasons );
    ABC_FREE( p->pSeen );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Records a SAT variable's interpolation partition.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Imc_PrfSetVar( Imc_Prf_t * p, int Var, int fPartA )
{
    assert( Var >= 0 );
    Vec_IntFillExtra( p->vPartA, Var + 1, p->fDual );
    Vec_StrFillExtra( p->vVarSet, Var + 1, 0 );
    assert( !p->fIncremental || !Vec_StrEntry(p->vVarSet, Var) ||
        Vec_IntEntry(p->vPartA, Var) == (fPartA ^ p->fDual) );
    Vec_StrWriteEntry( p->vVarSet, Var, 1 );
    Vec_IntWriteEntry( p->vPartA, Var, fPartA ^ p->fDual );
}

/**Function*************************************************************

  Synopsis    [Checks that the shared-variable interface has not changed.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Imc_PrfAssertGlobals( Imc_Prf_t * p, Vec_Int_t * vGlobals )
{
    int i, Var;
    assert( Gia_ManCiNum(p->pGia) == Vec_IntSize(vGlobals) );
    Vec_IntForEachEntry( vGlobals, Var, i )
        assert( Var >= 0 && Var < Vec_IntSize(p->vGlobal) && Vec_IntEntry(p->vGlobal, Var) == i );
}

/**Function*************************************************************

  Synopsis    [Allocates a clause and its antecedent hints in the appropriate arena.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Imc_Cls_t * Imc_PrfClause( Imc_Prf_t * p, int * pLits, int nLits, int iInter, int fPartA, int * pHints, int nHints )
{
    Imc_Cls_t * pCls = (Imc_Cls_t *)Mem_FlexEntryFetch( fPartA >= 0 ? p->pRootsMem : p->pDerivedMem, sizeof(Imc_Cls_t) + sizeof(int) * (nLits + nHints) );
    pCls->nLits = nLits;
    pCls->iInter = iInter;
    pCls->fPartA = fPartA;
    pCls->nHints = nHints;
    pCls->fUsed = 0;
    if ( nLits )
        memcpy( pCls->pLits, pLits, sizeof(int) * nLits );
    if ( nHints )
        memcpy( pCls->pLits + nLits, pHints, sizeof(int) * nHints );
    return pCls;
}

/**Function*************************************************************

  Synopsis    [Registers and labels an original clause after validating its partition.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Imc_PrfAddRoot( Imc_Prf_t * p, int * pLits, int nLits, int fPartA )
{
    int i, Var, iGlobal, iInter = (fPartA ^ p->fDual) ? 0 : 1;
    if ( p->fFailed )
        return -1;
    if ( p->fIncremental )
        for ( i = 0; i < nLits; i++ )
        {
            Var = Abc_Lit2Var(pLits[i]);
            iGlobal = Var < Vec_IntSize(p->vGlobal) ? Vec_IntEntry(p->vGlobal, Var) : -1;
            // Persistent labels require every local literal of an original
            // clause to belong to that clause's side, including release builds.
            if ( Var >= Vec_IntSize(p->vPartA) ||
                 (iGlobal < 0 && Vec_IntEntry(p->vPartA, Var) != (fPartA ^ p->fDual)) )
            {
                p->fFailed = 1;
                return -1;
            }
            Vec_StrFillExtra( p->vVarSet, Var + 1, 0 );
            Vec_StrWriteEntry( p->vVarSet, Var, 1 );
        }
    if ( !p->fPudlak && (fPartA ^ p->fDual) )
        for ( i = 0; i < nLits; i++ )
        {
            Var = Abc_Lit2Var(pLits[i]);
            iGlobal = Var < Vec_IntSize(p->vGlobal) ? Vec_IntEntry(p->vGlobal, Var) : -1;
            if ( iGlobal >= 0 )
                iInter = Gia_ManHashOr( p->pGia, iInter, Abc_Var2Lit(Gia_ObjId(p->pGia, Gia_ManCi(p->pGia, iGlobal)), Abc_LitIsCompl(pLits[i])) );
        }
    Vec_PtrPush( p->fIncremental ? p->vPending : p->vClauses, Imc_PrfClause(p, pLits, nLits, iInter, fPartA, NULL, 0) );
    p->nRoots++;
    return Vec_PtrSize(p->vClauses) - 1;
}

/**Function*************************************************************

  Synopsis    [Checks A implies I and I contradicts B with a separate solver.]

  Description [This optional check uses the original partitioned clauses
  and the final simplified interpolant, independently of proof replay.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Imc_PrfCheck( Imc_Prf_t * p, Gia_Man_t * pImage, Vec_Int_t * vGlobals, int nVars, int LitA, int LitB, int nConfLimit, abctime TimeStop )
{
    Imc_Cls_t * pCls;
    int i, Part, Lit, Status;
    for ( Part = 0; Part < 2; Part++ )
    {
        Imc_Sat_t Sat;
        memset( &Sat, 0, sizeof(Imc_Sat_t) );
        Sat.pSat = sat_solver_new();
        Sat.nVars = nVars;
        sat_solver_setnvars( Sat.pSat, nVars );
        sat_solver_set_runtime_limit( Sat.pSat, TimeStop );
        if ( Imc_ManStopActive() ) sat_solver_set_stop_func( Sat.pSat, Imc_ManStopId );
        for ( i = 1; i < Vec_PtrSize(p->vClauses); i++ )
        {
            pCls = (Imc_Cls_t *)Vec_PtrEntry( p->vClauses, i );
            if ( pCls && pCls->fPartA == Part )
                Imc_SatAddClause( &Sat, pCls->pLits, pCls->nLits, 0 );
        }
        Lit = Part ? LitA : LitB;
        Imc_SatAddClause( &Sat, &Lit, 1, 0 );
        Lit = Imc_SatAddGia( &Sat, pImage, vGlobals, 0 ) ^ Part;
        Status = Sat.fUnsat ? l_False : sat_solver_solve(Sat.pSat, &Lit, &Lit + 1, nConfLimit, 0, 0, 0);
        sat_solver_delete( Sat.pSat );
        if ( Status != l_False )
        {
            if ( Status == l_True )
                Abc_Print( -1, "IMC: Interpolant check failed for partition %c.\n", Part ? 'A' : 'B' );
            return Status == l_True ? 0 : -1;
        }
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Resets a nonincremental proof reader for another refutation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
void Imc_PrfRestart( Imc_Prf_t * p )
{
    Imc_Cls_t * pCls;
    int i, k, Var, iGlobal, nInputs = Gia_ManCiNum(p->pGia);
    // Incremental clause labels remain valid in the same hashed manager.
    if ( p->fIncremental )
        return;
    Gia_ManStop( p->pGia );
    p->pGia = Gia_ManStart( 1000 );
    p->pGia->fAddStrash = 1;
    Gia_ManHashStart( p->pGia );
    for ( i = 0; i < nInputs; i++ )
        Gia_ManAppendCi( p->pGia );
    for ( i = 1; i < Vec_PtrSize(p->vClauses); i++ )
    {
        pCls = (Imc_Cls_t *)Vec_PtrEntry( p->vClauses, i );
        if ( pCls == NULL || pCls->fPartA < 0 )
            continue;
        pCls->iInter = (pCls->fPartA ^ p->fDual) ? 0 : 1;
        if ( p->fPudlak || !(pCls->fPartA ^ p->fDual) )
            continue;
        for ( k = 0; k < pCls->nLits; k++ )
        {
            Var = Abc_Lit2Var(pCls->pLits[k]);
            iGlobal = Var < Vec_IntSize(p->vGlobal) ? Vec_IntEntry(p->vGlobal, Var) : -1;
            if ( iGlobal >= 0 )
                pCls->iInter = Gia_ManHashOr( p->pGia, pCls->iInter, Abc_Var2Lit(Gia_ObjId(p->pGia, Gia_ManCi(p->pGia, iGlobal)), Abc_LitIsCompl(pCls->pLits[k])) );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Interpolates only resolution chains used by the refutation.]

  Description [The record layout is the one used by satProof.c. The two
  low bits of an antecedent indicate an original clause and an A-local
  pivot, respectively. Sorting reachable handles gives topological order
  without recursion, even for very deep resolution proofs.]

  SideEffects [Uses the proof records' scratch labels.]

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Imc_PrfReadSat( Imc_Prf_t * p, sat_solver2 * pSat, abctime TimeStop )
{
    typedef struct Imc_Res_t_ Imc_Res_t;
    struct Imc_Res_t_
    {
        unsigned learnt : 1;
        unsigned mark   : 1;
        unsigned partA  : 1;
        unsigned nEnts  : 29;
        int Id;
        int pEnts[0];
    };
    Vec_Int_t * vUsed = Vec_IntAlloc( 1000 );
    Gia_Man_t * pResult = NULL;
    Imc_Res_t * pNode, * pNext;
    Imc_Cls_t * pCls;
    int i, k, h, Entry, Lit, iInter;
    if ( pSat->hProofLast <= 0 )
        goto finish;
    Vec_IntPush( vUsed, pSat->hProofLast );
    pNode = (Imc_Res_t *)Vec_SetEntry( pSat->pPrf1, pSat->hProofLast );
    pNode->Id = -1;
    Vec_IntForEachEntry( vUsed, h, i )
    {
        if ( (i & 1023) == 0 && Imc_ManCheckStop(TimeStop) )
            goto finish;
        pNode = (Imc_Res_t *)Vec_SetEntry( pSat->pPrf1, h );
        for ( k = 0; k < (int)pNode->nEnts; k++ )
        {
            Entry = pNode->pEnts[k];
            if ( Entry & 1 )
                continue;
            pNext = (Imc_Res_t *)Vec_SetEntry( pSat->pPrf1, Entry >> 2 );
            if ( pNext->Id == -1 )
                continue;
            pNext->Id = -1;
            Vec_IntPush( vUsed, Entry >> 2 );
        }
    }
    Vec_IntSort( vUsed, 0 );
    Vec_IntForEachEntry( vUsed, h, i )
    {
        if ( (i & 1023) == 0 && Imc_ManCheckStop(TimeStop) )
            goto finish;
        pNode = (Imc_Res_t *)Vec_SetEntry( pSat->pPrf1, h );
        iInter = -1;
        for ( k = 0; k < (int)pNode->nEnts; k++ )
        {
            Entry = pNode->pEnts[k];
            if ( Entry & 1 )
            {
                if ( (Entry >> 2) <= 0 || (Entry >> 2) >= Vec_PtrSize(p->vClauses) )
                    goto finish;
                pCls = (Imc_Cls_t *)Vec_PtrEntry( p->vClauses, Entry >> 2 );
                if ( pCls == NULL || pCls->iInter < 0 )
                    goto finish;
                Lit = pCls->iInter;
            }
            else
            {
                pNext = (Imc_Res_t *)Vec_SetEntry( pSat->pPrf1, Entry >> 2 );
                assert( pNext->Id > 0 );
                Lit = pNext->Id - 1;
            }
            iInter = k == 0 ? Lit : (Entry & 2) ? Gia_ManHashOr(p->pGia, iInter, Lit) : Gia_ManHashAnd(p->pGia, iInter, Lit);
        }
        assert( iInter >= 0 );
        pNode->Id = iInter + 1;
    }
    pNode = (Imc_Res_t *)Vec_SetEntry( pSat->pPrf1, pSat->hProofLast );
    Gia_ManAppendCo( p->pGia, (pNode->Id - 1) ^ p->fDual );
    pResult = Gia_ManCleanup( p->pGia );
finish:
    Vec_IntForEachEntry( vUsed, h, i )
    {
        pNode = (Imc_Res_t *)Vec_SetEntry( pSat->pPrf1, h );
        pNode->Id = 0;
    }
    Vec_IntFree( vUsed );
    return pResult;
}

/**Function*************************************************************

  Synopsis    [Looks up a recorded clause by its proof identifier.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Imc_Cls_t * Imc_PrfLookup( Imc_Prf_t * p, int Id )
{
    return Id > 0 && Id < Vec_PtrSize(p->vClauses) ? (Imc_Cls_t *)Vec_PtrEntry(p->vClauses, Id) : NULL;
}

/**Function*************************************************************

  Synopsis    [Records a variable whose proof-replay marks need clearing.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_PrfMark( Imc_Prf_t * p, int Var )
{
    if ( !p->pSeen[Var] )
    {
        p->pSeen[Var] = 1;
        Vec_IntPush( p->vSeen, Var );
    }
}

/**Function*************************************************************

  Synopsis    [Records a resolution chain from reverse unit propagation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_PrfTrace( Imc_Prf_t * p, Vec_Int_t * vLits, Vec_Int_t * vChain )
{
    Imc_Cls_t * pCls = NULL;
    int i, j, Var, Lit, Id = -1, nUndef, Unit = -1, nAss, fConflict = 0;
    Vec_IntClear( p->vTrail );
    Vec_IntClear( p->vSeen );
    Vec_IntClear( p->vSteps );
    Vec_IntForEachEntry( vLits, Lit, i )
    {
        Var = Abc_Lit2Var(Lit);
        if ( p->pValues[Var] != -1 )
            goto finish;
        p->pValues[Var] = Abc_LitIsCompl(Lit);
        Vec_IntPush( p->vTrail, Var );
    }
    nAss = Vec_IntSize(p->vTrail);
    // LRAT supplies the exact propagation order; no watch-list replay is
    // necessary. Only reasons used by the final conflict are resolved.
    Vec_IntForEachEntry( vChain, Id, i )
    {
        pCls = Imc_PrfLookup( p, Id );
        if ( pCls == NULL )
            goto finish;
        nUndef = 0;
        for ( j = 0; j < pCls->nLits; j++ )
        {
            Lit = pCls->pLits[j];
            Var = Abc_Lit2Var(Lit);
            if ( p->pValues[Var] == -1 )
                Unit = Lit, nUndef++;
            else if ( p->pValues[Var] != Abc_LitIsCompl(Lit) )
                break;
        }
        if ( j < pCls->nLits )
            continue;
        if ( nUndef > 1 )
            goto finish;
        if ( nUndef == 0 )
        {
            fConflict = 1;
            break;
        }
        Var = Abc_Lit2Var(Unit);
        p->pValues[Var] = !Abc_LitIsCompl(Unit);
        p->pReasons[Var] = Id;
        Vec_IntPush( p->vTrail, Var );
    }
    if ( !fConflict )
        goto finish;
    Vec_IntPush( p->vSteps, Id );
    for ( j = 0; j < pCls->nLits; j++ )
        Imc_PrfMark( p, Abc_Lit2Var(pCls->pLits[j]) );
    for ( i = Vec_IntSize(p->vTrail) - 1; i >= nAss; i-- )
    {
        Var = Vec_IntEntry(p->vTrail, i);
        if ( !p->pSeen[Var] )
            continue;
        pCls = Imc_PrfLookup( p, p->pReasons[Var] );
        assert( pCls != NULL );
        Vec_IntPush( p->vSteps, Abc_Var2Lit(Var, p->pValues[Var]) );
        Vec_IntPush( p->vSteps, p->pReasons[Var] );
        p->pSeen[Var] = 0;
        for ( j = 0; j < pCls->nLits; j++ )
            if ( Abc_Lit2Var(pCls->pLits[j]) != Var )
                Imc_PrfMark( p, Abc_Lit2Var(pCls->pLits[j]) );
    }
finish:
    Vec_IntForEachEntry( p->vTrail, Var, i )
        p->pValues[Var] = -1;
    Vec_IntForEachEntry( p->vSeen, Var, i )
        p->pSeen[Var] = 0;
    return fConflict;
}

// Fold the same resolution sequence under any McMillan/Pudlak labeling.
/**Function*************************************************************

  Synopsis    [Evaluates one interpolation labeling over a recorded resolution chain.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_PrfFold( Imc_Prf_t * p, Gia_Man_t * pGia, int fDual, int fPudlak,
    Vec_Int_t * vLabels, Vec_Int_t * vOrder )
{
    int i, Id = Vec_IntEntry(p->vSteps, 0), Pivot, Var, Global, Lit, Label;
    int Inter = vLabels ? Vec_IntEntry(vLabels, Vec_IntEntry(vOrder, Id)) : Imc_PrfLookup(p, Id)->iInter;
    for ( i = 1; i < Vec_IntSize(p->vSteps); i += 2 )
    {
        Pivot = Vec_IntEntry(p->vSteps, i);
        Var = Abc_Lit2Var(Pivot);
        Id = Vec_IntEntry(p->vSteps, i + 1);
        Label = vLabels ? Vec_IntEntry(vLabels, Vec_IntEntry(vOrder, Id)) : Imc_PrfLookup(p, Id)->iInter;
        Global = Var < Vec_IntSize(p->vGlobal) ? Vec_IntEntry(p->vGlobal, Var) : -1;
        if ( fPudlak && Global >= 0 )
        {
            Lit = Gia_Obj2Lit(pGia, Gia_ManCi(pGia, Global)) ^ Abc_LitIsCompl(Pivot);
            Inter = Gia_ManHashAnd( pGia, Gia_ManHashOr(pGia, Inter, Lit), Gia_ManHashOr(pGia, Label, Lit ^ 1) );
        }
        else if ( Global < 0 && (Vec_IntEntry(p->vPartA, Var) ^ p->fDual ^ fDual) )
            Inter = Gia_ManHashOr( pGia, Inter, Label );
        else
            Inter = Gia_ManHashAnd( pGia, Inter, Label );
    }
    return Inter;
}

/**Function*************************************************************

  Synopsis    [Replays a clause derivation with the selected interpolation labeling.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_PrfReplay( Imc_Prf_t * p, Vec_Int_t * vLits, Vec_Int_t * vChain )
{
    return Imc_PrfTrace(p, vLits, vChain) ? Imc_PrfFold(p, p->pGia, p->fDual, p->fPudlak, NULL, NULL) : -1;
}

// Copy one label cone iteratively, retaining all shared input positions.
// The persistent incremental manager has no COs and is never renumbered.
/**Function*************************************************************

  Synopsis    [Extracts the reachable interpolant cone while preserving its input interface.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Imc_PrfExtract( Gia_Man_t * pGia, int Lit )
{
    Vec_Int_t * vStack = Vec_IntAlloc( 64 );
    Gia_Man_t * pNew = Gia_ManStart( 1000 );
    Gia_Obj_t * pObj;
    int i;
    Gia_ManIncrementTravId( pGia );
    Vec_IntPush( vStack, Abc_Lit2Var(Lit) );
    while ( Vec_IntSize(vStack) )
    {
        pObj = Gia_ManObj( pGia, Vec_IntPop(vStack) );
        if ( Gia_ObjIsTravIdCurrent(pGia, pObj) )
            continue;
        Gia_ObjSetTravIdCurrent( pGia, pObj );
        if ( Gia_ObjIsAnd(pObj) )
        {
            Vec_IntPush( vStack, Gia_ObjFaninId0p(pGia, pObj) );
            Vec_IntPush( vStack, Gia_ObjFaninId1p(pGia, pObj) );
        }
    }
    Gia_ManConst0(pGia)->Value = 0;
    Gia_ManForEachCi( pGia, pObj, i )
        pObj->Value = Gia_ManAppendCi( pNew );
    Gia_ManForEachAnd( pGia, pObj, i )
        if ( Gia_ObjIsTravIdCurrent(pGia, pObj) )
            pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManAppendCo( pNew, Gia_ManObj(pGia, Abc_Lit2Var(Lit))->Value ^ Abc_LitIsCompl(Lit) );
    Vec_IntFree( vStack );
    return pNew;
}

typedef struct Imc_Read_t_ Imc_Read_t;
struct Imc_Read_t_
{
    FILE * pFile;
    ABC_INT64_T Offset;
    int Pos, Size;
    unsigned char * Buffer;
};

/**Function*************************************************************

  Synopsis    [Reads a proof byte through the reader's buffered stream.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_PrfByte( Imc_Read_t * p )
{
    if ( p->Pos == p->Size )
    {
        p->Offset += p->Size;
        p->Pos = 0;
        p->Size = fread( p->Buffer, 1, 65536, p->pFile );
        if ( p->Size == 0 )
            return EOF;
    }
    return p->Buffer[p->Pos++];
}

/**Function*************************************************************

  Synopsis    [Decodes a signed variable-length proof number with range checks.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_PrfReadNum( Imc_Read_t * pRead, int * pNum )
{
    word Value = 0;
    int c, Shift = 0;
    do
    {
        c = Imc_PrfByte( pRead );
        if ( c == EOF || Shift >= 63 )
            return 0;
        Value |= (word)(c & 127) << Shift;
        Shift += 7;
    }
    while ( c & 128 );
    if ( (Value >> 1) > INT_MAX )
        return 0;
    *pNum = (Value & 1) ? -(int)(Value >> 1) : (int)(Value >> 1);
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks the proof-minimization deadline.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_PrfMinimizeStop( void * pData )
{
    return Imc_ManCheckStop(*(abctime *)pData);
}

/**Function*************************************************************

  Synopsis    [Re-solves the used proof core to seek a smaller interpolant.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Imc_PrfMinimize( Imc_Prf_t * p, int nVars, abctime TimeStop )
{
    Imc_Sat_t Sat;
    Vec_Int_t * vGlobals;
    Imc_Prf_t * pMini;
    Imc_Cls_t * pCls;
    Gia_Man_t * pResult = NULL;
    CCaDiCaL * pCad;
    FILE * pFile;
    abctime TimeMini = TimeStop;
    int i, Var, nRoots = 0;
    Vec_PtrForEachEntry( Imc_Cls_t *, p->vClauses, pCls, i )
        nRoots += pCls && pCls->fPartA >= 0 && pCls->fUsed;
    if ( nRoots < 64 || nRoots * 2 > p->nRoots )
        return NULL;
    if ( Imc_PrfMinimizeStop(&TimeMini) )
        return NULL;
    pFile = Imc_ProofFile();
    if ( pFile == NULL )
        return NULL;
    vGlobals = Vec_IntStartFull( Gia_ManCiNum(p->pGia) );
    Vec_IntForEachEntry( p->vGlobal, Var, i )
        if ( Var >= 0 )
            Vec_IntWriteEntry( vGlobals, Var, i );
    pMini = Imc_PrfStart( vGlobals, 0, nVars, p->fDual, p->fPudlak, 0 );
    Vec_IntFree( pMini->vPartA );
    pMini->vPartA = Vec_IntDup( p->vPartA );
    Vec_IntFree( vGlobals );
    pCad = ccadical_init();
    memset( &Sat, 0, sizeof(Sat) );
    Sat.pCad = pCad;
    Sat.pPrf = pMini;
    Sat.nVars = nVars;
    ccadical_set_option( pCad, "quiet", 1 );
    ccadical_set_option( pCad, "congruence", 0 );
    ccadical_set_option( pCad, "lrat", 1 );
    ccadical_set_option( pCad, "binary", 1 );
    ccadical_set_option( pCad, "factor", 0 );
    ccadical_set_option( pCad, "condition", 0 );
    ccadical_limit( pCad, "conflicts", 5000 );
    ccadical_set_terminate( pCad, &TimeMini, Imc_PrfMinimizeStop );
    if ( !ccadical_trace_proof(pCad, pFile, "imc-core-lrat") )
        goto finish;
    // The used original clauses form an UNSAT subset. Interpolating a
    // refutation of this subset also interpolates the original pair.
    Vec_PtrForEachEntry( Imc_Cls_t *, p->vClauses, pCls, i )
        if ( pCls && pCls->fPartA >= 0 && pCls->fUsed )
        {
            Imc_SatAddClause( &Sat, pCls->pLits, pCls->nLits, pCls->fPartA );
        }
    if ( ccadical_solve(pCad) == 20 )
    {
        ccadical_close_proof( pCad );
        fflush( pFile );
        pResult = Imc_PrfRead( pMini, pFile, Sat.nVars, 0, 0, TimeMini );
    }
finish:
    ccadical_release( pCad );
    Imc_PrfStop( pMini );
    fclose( pFile );
    return pResult;
}

/**Function*************************************************************

  Synopsis    [Reports whether proof-core minimization improved the interpolant.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Imc_PrfWasMinimized( Imc_Prf_t * p )
{
    return p->fMinimized;
}

/**Function*************************************************************

  Synopsis    [Adds an ABC-literal clause to a plain CaDiCaL solver.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Imc_PrfAddPlain( CCaDiCaL * pCad, int * pLits, int nLits )
{
    int i;
    for ( i = 0; i < nLits; i++ )
        ccadical_add( pCad, (Abc_Lit2Var(pLits[i]) + 1) * (Abc_LitIsCompl(pLits[i]) ? -1 : 1) );
    ccadical_add( pCad, 0 );
}

/**Function*************************************************************

  Synopsis    [Weakens an interpolant using an UNSAT assumption core.]

  Description [A monotone AND/OR encoding keeps the two polarities of a
  shared internal node separate. Each internal formula can be replaced
  by true by releasing its selector. An UNSAT core selects the formulas
  needed to contradict B. Replacing the others by true weakens I, so A
  still implies the result. The query proves that it still contradicts B.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Imc_PrfWeaken( Imc_Prf_t * p, Gia_Man_t * pImage, Vec_Int_t * vGlobals, int nVars, int LitB, abctime TimeStop )
{
    Vec_Int_t * vStack = NULL, * vMap = NULL, * vSelect = NULL, * vCopy = NULL;
    Vec_Str_t * vUsed = NULL;
    Gia_Man_t * pNew = NULL, * pResult = NULL;
    CCaDiCaL * pCad = NULL;
    Gia_Obj_t * pObj;
    Imc_Cls_t * pCls;
    abctime TimeCore = TimeStop;
    int i, k, Lit, Lit0, Lit1, Out, Sel, Lits[4];
    int Root = Gia_ObjFaninLit0p(pImage, Gia_ManPo(pImage, 0));
    int nLits = 2 * Gia_ManObjNum(pImage), nRemoved = 0;
    if ( Gia_ManAndNum(pImage) < 64 || Gia_ManAndNum(pImage) > 200000 || p->nRoots > 200000 )
        return NULL;
    if ( Imc_PrfMinimizeStop(&TimeCore) )
        return NULL;
    vStack = Vec_IntAlloc( 32 );
    vUsed = Vec_StrStart( nLits );
    vMap = Vec_IntStartFull( nLits );
    vSelect = Vec_IntStartFull( nLits );
    Vec_IntPush( vStack, Root );
    while ( Vec_IntSize(vStack) )
    {
        Lit = Vec_IntPop( vStack );
        if ( Vec_StrEntry(vUsed, Lit) )
            continue;
        Vec_StrWriteEntry( vUsed, Lit, 1 );
        pObj = Gia_ManObj( pImage, Abc_Lit2Var(Lit) );
        if ( Gia_ObjIsAnd(pObj) )
        {
            Vec_IntPush( vStack, Gia_ObjFaninLit0p(pImage, pObj) ^ Abc_LitIsCompl(Lit) );
            Vec_IntPush( vStack, Gia_ObjFaninLit1p(pImage, pObj) ^ Abc_LitIsCompl(Lit) );
        }
    }
    pCad = ccadical_init();
    ccadical_set_option( pCad, "quiet", 1 );
    ccadical_set_option( pCad, "congruence", 0 );
    ccadical_set_option( pCad, "inprocessing", 0 );
    ccadical_set_terminate( pCad, &TimeCore, Imc_PrfMinimizeStop );
    Vec_PtrForEachEntry( Imc_Cls_t *, p->vClauses, pCls, i )
    {
        if ( (i & 1023) == 0 && Imc_PrfMinimizeStop(&TimeCore) )
            goto finish;
        if ( pCls && pCls->fPartA == 0 )
            Imc_PrfAddPlain( pCad, pCls->pLits, pCls->nLits );
    }
    Imc_PrfAddPlain( pCad, &LitB, 1 );
    Lit = Abc_Var2Lit( nVars++, 0 );
    Vec_IntWriteEntry( vMap, 0, Lit );
    Vec_IntWriteEntry( vMap, 1, Lit ^ 1 );
    Lit ^= 1;
    Imc_PrfAddPlain( pCad, &Lit, 1 );
    Gia_ManForEachCi( pImage, pObj, i )
    {
        for ( k = 0; k < 2; k++ )
        {
            Lit = Gia_Obj2Lit( pImage, pObj ) ^ k;
            if ( !Vec_StrEntry(vUsed, Lit) )
                continue;
            Out = Abc_Var2Lit( nVars++, 0 );
            Sel = Abc_Var2Lit( nVars++, 0 );
            Vec_IntWriteEntry( vMap, Lit, Out );
            Vec_IntWriteEntry( vSelect, Lit, Sel );
            Lits[0] = Out ^ 1;
            Lits[1] = Sel ^ 1;
            Lits[2] = Abc_Var2Lit( Vec_IntEntry(vGlobals, i), k );
            Imc_PrfAddPlain( pCad, Lits, 3 );
        }
    }
    Gia_ManForEachAnd( pImage, pObj, i )
    {
        if ( (i & 1023) == 0 && Imc_PrfMinimizeStop(&TimeCore) )
            goto finish;
        for ( k = 0; k < 2; k++ )
        {
            Lit = Abc_Var2Lit( i, k );
            if ( !Vec_StrEntry(vUsed, Lit) )
                continue;
            Out = Abc_Var2Lit( nVars++, 0 );
            Sel = Abc_Var2Lit( nVars++, 0 );
            Vec_IntWriteEntry( vMap, Lit, Out );
            Vec_IntWriteEntry( vSelect, Lit, Sel );
            Lit0 = Vec_IntEntry( vMap, Gia_ObjFaninLit0p(pImage, pObj) ^ k );
            Lit1 = Vec_IntEntry( vMap, Gia_ObjFaninLit1p(pImage, pObj) ^ k );
            assert( Lit0 >= 0 && Lit1 >= 0 );
            // Only the forward implication is needed in this monotone
            // encoding: output true implies its enabled AND/OR formula.
            Lits[0] = Out ^ 1;
            Lits[1] = Sel ^ 1;
            Lits[2] = Lit0;
            if ( k )
            {
                Lits[3] = Lit1;
                Imc_PrfAddPlain( pCad, Lits, 4 );
            }
            else
            {
                Imc_PrfAddPlain( pCad, Lits, 3 );
                Lits[2] = Lit1;
                Imc_PrfAddPlain( pCad, Lits, 3 );
            }
        }
    }
    Lit = Vec_IntEntry( vMap, Root );
    Imc_PrfAddPlain( pCad, &Lit, 1 );
    Vec_IntForEachEntry( vSelect, Sel, i )
        if ( Sel >= 0 )
            ccadical_assume( pCad, Abc_Lit2Var(Sel) + 1 );
    ccadical_limit( pCad, "conflicts", 3000 );
    if ( ccadical_solve(pCad) != 20 )
        goto finish;
    Vec_IntForEachEntry( vSelect, Sel, i )
        if ( Sel >= 0 && !ccadical_failed(pCad, Abc_Lit2Var(Sel) + 1) )
            nRemoved++;
    if ( nRemoved == 0 )
        goto finish;
    pNew = Gia_ManStart( Gia_ManObjNum(pImage) );
    Gia_ManHashStart( pNew );
    vCopy = Vec_IntStartFull( nLits );
    Vec_IntWriteEntry( vCopy, 0, 0 );
    Vec_IntWriteEntry( vCopy, 1, 1 );
    Gia_ManForEachCi( pImage, pObj, i )
    {
        Lit = Gia_Obj2Lit( pImage, pObj );
        Out = Gia_ManAppendCi( pNew );
        for ( k = 0; k < 2; k++ )
        {
            Sel = Vec_IntEntry( vSelect, Lit ^ k );
            Vec_IntWriteEntry( vCopy, Lit ^ k,
                Sel >= 0 && ccadical_failed(pCad, Abc_Lit2Var(Sel) + 1) ? Out ^ k : 1 );
        }
    }
    Gia_ManForEachAnd( pImage, pObj, i )
        for ( k = 0; k < 2; k++ )
        {
            Lit = Abc_Var2Lit( i, k );
            Sel = Vec_IntEntry( vSelect, Lit );
            if ( Sel < 0 )
                continue;
            Out = 1;
            if ( ccadical_failed(pCad, Abc_Lit2Var(Sel) + 1) )
            {
                Lit0 = Vec_IntEntry( vCopy, Gia_ObjFaninLit0p(pImage, pObj) ^ k );
                Lit1 = Vec_IntEntry( vCopy, Gia_ObjFaninLit1p(pImage, pObj) ^ k );
                assert( Lit0 >= 0 && Lit1 >= 0 );
                Out = k ? Gia_ManHashOr(pNew, Lit0, Lit1) : Gia_ManHashAnd(pNew, Lit0, Lit1);
            }
            Vec_IntWriteEntry( vCopy, Lit, Out );
        }
    Gia_ManAppendCo( pNew, Vec_IntEntry(vCopy, Root) );
    Gia_ManHashStop( pNew );
    pResult = Gia_ManCleanup( pNew );
    if ( Gia_ManAndNum(pResult) >= Gia_ManAndNum(pImage) )
        Gia_ManStopP( &pResult );
finish:
    if ( pCad )
        ccadical_release( pCad );
    Gia_ManStopP( &pNew );
    Vec_IntFreeP( &vStack );
    Vec_IntFreeP( &vMap );
    Vec_IntFreeP( &vSelect );
    Vec_IntFreeP( &vCopy );
    Vec_StrFreeP( &vUsed );
    return pResult;
}

// Clause IDs are monotonic but may have small gaps (hidden conclusions).
// Reject corrupt sparse IDs before Id+1 can overflow or allocate gigabytes.
/**Function*************************************************************

  Synopsis    [Rejects nonpositive, overflowing, and excessively sparse clause identifiers.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_PrfValidId( Imc_Prf_t * p, int Id )
{
    int Size = Vec_PtrSize( p->vClauses );
    return Id > 0 && Id < INT_MAX &&
        (word)Id <= (word)Size + Abc_MaxInt( 1024, Size );
}

// Replay propagation once per reachable clause, then fold every distinct
// labeling over the recorded pivots in the same topological pass. Plain
// and dual Pudlak agree as functions but can have different AIG sizes.
/**Function*************************************************************

  Synopsis    [Folds the selected labelings over the reachable proof and chooses the smallest.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Gia_Man_t * Imc_PrfInterpolate( Imc_Prf_t * p, Vec_Int_t * vUsed, int Root, int fAuto, abctime TimeStop )
{
    Gia_Man_t * Gias[4] = { p->pGia, NULL, NULL, NULL }, * pResult = NULL, * pCandidate;
    Vec_Int_t * Labels[4] = { NULL, NULL, NULL, NULL }, * vOrder = NULL;
    int Modes[4][2], Choices[4][2] = { {0, 0}, {1, 0}, {0, 1}, {1, 1} };
    int nModes = 1, i, k, m, Id, Var, Global, Label;
    Imc_Cls_t * pCls;
    Modes[0][0] = p->fDual;
    Modes[0][1] = p->fPudlak;
    for ( k = 0; fAuto && k < 4; k++ )
        if ( (fAuto != 2 || Choices[k][1] == p->fPudlak) &&
             (Choices[k][0] != p->fDual || Choices[k][1] != p->fPudlak) )
        {
            Modes[nModes][0] = Choices[k][0];
            Modes[nModes++][1] = Choices[k][1];
        }
    if ( nModes > 1 )
    {
        vOrder = Vec_IntStartFull( Vec_PtrSize(p->vClauses) );
        Vec_IntForEachEntry( vUsed, Id, i )
            Vec_IntWriteEntry( vOrder, Id, i );
        for ( m = 0; m < nModes; m++ )
        {
            Labels[m] = Vec_IntStartFull( Vec_IntSize(vUsed) );
            if ( m == 0 )
                continue;
            Gias[m] = Gia_ManStart( 1000 );
            Gias[m]->fAddStrash = 1;
            Gia_ManHashStart( Gias[m] );
            for ( i = 0; i < Gia_ManCiNum(p->pGia); i++ )
                Gia_ManAppendCi( Gias[m] );
        }
    }
    Vec_IntForEachEntry( vUsed, Id, i )
    {
        if ( (i & 255) == 0 && Imc_ManCheckStop(TimeStop) )
            goto finish;
        pCls = Imc_PrfLookup( p, Id );
        if ( pCls->fPartA < 0 )
        {
            Vec_Int_t Lits = { pCls->nLits, pCls->nLits, pCls->pLits };
            Vec_Int_t Chain = { pCls->nHints, pCls->nHints, pCls->pLits + pCls->nLits };
            if ( !Imc_PrfTrace(p, &Lits, &Chain) )
                goto finish;
        }
        for ( m = 0; m < nModes; m++ )
        {
            if ( pCls->fPartA < 0 )
                Label = Imc_PrfFold( p, Gias[m], Modes[m][0], Modes[m][1], Labels[m], vOrder );
            else
            {
                Label = (pCls->fPartA ^ Modes[m][0]) ? 0 : 1;
                if ( !Modes[m][1] && !Label )
                    for ( k = 0; k < pCls->nLits; k++ )
                    {
                        Var = Abc_Lit2Var(pCls->pLits[k]);
                        Global = Var < Vec_IntSize(p->vGlobal) ? Vec_IntEntry(p->vGlobal, Var) : -1;
                        if ( Global >= 0 )
                            Label = Gia_ManHashOr( Gias[m], Label,
                                Gia_Obj2Lit(Gias[m], Gia_ManCi(Gias[m], Global)) ^ Abc_LitIsCompl(pCls->pLits[k]) );
                    }
            }
            if ( Labels[m] )
                Vec_IntWriteEntry( Labels[m], i, Label );
            if ( m == 0 )
                pCls->iInter = Label;
        }
    }
    for ( m = 0; m < nModes; m++ )
    {
        Label = Labels[m] ? Vec_IntEntry(Labels[m], Vec_IntEntry(vOrder, Root)) : Imc_PrfLookup(p, Root)->iInter;
        pCandidate = Imc_PrfExtract( Gias[m], Label ^ Modes[m][0] );
        if ( pResult == NULL || Gia_ManAndNum(pCandidate) < Gia_ManAndNum(pResult) )
        {
            Gia_ManStopP( &pResult );
            pResult = pCandidate;
        }
        else
            Gia_ManStop( pCandidate );
    }
finish:
    for ( m = 0; m < nModes; m++ )
    {
        Vec_IntFreeP( &Labels[m] );
        if ( m ) Gia_ManStopP( &Gias[m] );
    }
    Vec_IntFreeP( &vOrder );
    return pResult;
}

/**Function*************************************************************

  Synopsis    [Reads a binary LRAT refutation and constructs its interpolant.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Imc_PrfRead( Imc_Prf_t * p, FILE * pFile, int nVars, int fAutoItp, int fMinimize, abctime TimeStop )
{
    Imc_Read_t Read;
    Vec_Int_t * vLits = Vec_IntAlloc( 32 );
    Vec_Int_t * vChain = Vec_IntAlloc( 100 );
    Vec_Int_t * vUsed = Vec_IntAlloc( 1000 );
    Gia_Man_t * pResult = NULL;
    Imc_Cls_t * pCls, * pNext;
    int c, Id = 0, Num, i, k, iRoot = -1, nRecords = 0;
    if ( p->fRead )
    {
        Mem_FlexRestart( p->pDerivedMem );
        Vec_PtrShrink( p->vClauses, p->nRoots + 1 );
        Imc_PrfRestart( p );
    }
    p->fRead = 1;
    p->fMinimized = 0;
    Vec_PtrForEachEntry( Imc_Cls_t *, p->vClauses, pCls, i )
        if ( pCls )
            pCls->fUsed = 0;
    ABC_FREE( p->pValues );
    ABC_FREE( p->pReasons );
    ABC_FREE( p->pSeen );
    p->pValues = ABC_ALLOC( int, nVars );
    memset( p->pValues, 0xff, sizeof(int) * nVars );
    p->pReasons = ABC_CALLOC( int, nVars );
    p->pSeen = ABC_CALLOC( unsigned char, nVars );
    Vec_IntFillExtra( p->vPartA, nVars, p->fDual );
    rewind( pFile );
    memset( &Read, 0, sizeof(Read) );
    Read.Buffer = ABC_ALLOC( unsigned char, 65536 );
    Read.pFile = pFile;
    while ( (c = Imc_PrfByte(&Read)) != EOF )
    {
        if ( (nRecords++ & 1023) == 0 && Imc_ManCheckStop(TimeStop) )
            goto finish;
        if ( c == 'd' )
        {
            for ( ; ; )
            {
                if ( !Imc_PrfReadNum(&Read, &Num) )
                    goto invalid;
                if ( Num == 0 )
                    break;
            }
            continue;
        }
        if ( c != 'a' || !Imc_PrfReadNum(&Read, &Id) || !Imc_PrfValidId(p, Id) )
            goto invalid;
        Vec_IntClear( vLits );
        Vec_IntClear( vChain );
        for ( ; ; )
        {
            if ( !Imc_PrfReadNum(&Read, &Num) )
                goto invalid;
            if ( Num == 0 )
                break;
            if ( Abc_AbsInt(Num) > nVars )
                goto invalid;
            Vec_IntPush( vLits, Abc_Var2Lit(Abc_AbsInt(Num)-1, Num < 0) );
        }
        for ( ; ; )
        {
            if ( !Imc_PrfReadNum(&Read, &Num) || Num < 0 )
                goto invalid;
            if ( Num == 0 )
                break;
            if ( Num >= Id || Imc_PrfLookup(p, Num) == NULL )
                goto invalid;
            Vec_IntPush( vChain, Num );
        }
        if ( Imc_PrfLookup(p, Id) )
            goto invalid;
        Vec_PtrFillExtra( p->vClauses, Id + 1, NULL );
        Vec_PtrWriteEntry( p->vClauses, Id, Imc_PrfClause(p, Vec_IntArray(vLits), Vec_IntSize(vLits), -1, -1, Vec_IntArray(vChain), Vec_IntSize(vChain)) );
        if ( Vec_IntSize(vLits) == 0 )
        {
            iRoot = Id;
            break;
        }
    }
    if ( iRoot < 0 )
        goto finish;
    // Trim the proof before constructing any derived interpolants. LRAT
    // hints already describe the dependency DAG, so this needs no SAT
    // replay for clauses that do not contribute to the refutation.
    Vec_IntPush( vUsed, iRoot );
    Imc_PrfLookup(p, iRoot)->fUsed = 1;
    Vec_IntForEachEntry( vUsed, Id, i )
    {
        if ( (i & 1023) == 0 && Imc_ManCheckStop(TimeStop) )
            goto finish;
        pCls = Imc_PrfLookup( p, Id );
        for ( k = 0; k < pCls->nHints; k++ )
        {
            Num = pCls->pLits[pCls->nLits + k];
            pNext = Imc_PrfLookup( p, Num );
            if ( pNext->fUsed )
                continue;
            pNext->fUsed = 1;
            Vec_IntPush( vUsed, Num );
        }
    }
    Vec_IntSort( vUsed, 0 );
    pResult = Imc_PrfInterpolate( p, vUsed, iRoot, fAutoItp, TimeStop );
    if ( pResult == NULL )
    {
        if ( Imc_ManCheckStop(TimeStop) )
            goto finish;
        goto invalid;
    }
    if ( fMinimize && pResult && Gia_ManAndNum(pResult) >= 128 )
    {
        Gia_Man_t * pMini = Imc_PrfMinimize( p, nVars, TimeStop );
        if ( pMini && Gia_ManAndNum(pMini) < Gia_ManAndNum(pResult) )
        {
            Gia_ManStop( pResult );
            pResult = pMini;
            p->fMinimized = 1;
        }
        else
            Gia_ManStopP( &pMini );
    }
    goto finish;
invalid:
    Gia_ManStopP( &pResult );
    Abc_Print( -1, "IMC: Could not replay LRAT clause %d.\n", Id );
finish:
    ABC_FREE( Read.Buffer );
    Vec_IntFree( vLits );
    Vec_IntFree( vChain );
    Vec_IntFree( vUsed );
    return pResult;
}

/**Function*************************************************************

  Synopsis    [Decodes and validates an unsigned LIDRUP identifier.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Imc_PrfReadId( Imc_Read_t * pRead, int * pNum )
{
    // LIDRUP IDs and antecedents use the same signed encoding as literals.
    // This reader supports positive RUP antecedents, not negative RAT IDs.
    return Imc_PrfReadNum( pRead, pNum ) && *pNum >= 0;
}

/**Function*************************************************************

  Synopsis    [Reads one incremental LIDRUP query and interpolates its core.]

  Description [Original clauses carry explicit IDs, allowing roots and
  derived clauses to interleave. Deleted clauses remain available to replay
  ancestors of retained learned clauses. The conclusion derives the negated
  assumption core; resolving its local assumptions does not change its
  interpolant. No global variable is permitted as a query assumption.]

  SideEffects [Retains the proof DAG and advances the stream position.]

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Imc_PrfReadIncremental( Imc_Prf_t * p, FILE * pFile, int nVars, int LitA, int LitB, abctime TimeStop )
{
    Imc_Read_t Read;
    Vec_Int_t * vLits = Vec_IntAlloc( 32 );
    Vec_Int_t * vChain = Vec_IntAlloc( 100 );
    Vec_Int_t * vUsed = Vec_IntAlloc( 1000 );
    Gia_Man_t * pResult = NULL;
    Imc_Cls_t * pCls, * pNext;
    int c = 0, Id = 0, Num, Lit, i, k, nPending = 0, fQuery = 0, fFinal = 0, fUnknown = 0, nRecords = 0;
    memset(&Read, 0, sizeof(Read));
    if ( p->fFailed )
        goto finish;
    ABC_FREE( p->pValues );
    ABC_FREE( p->pReasons );
    ABC_FREE( p->pSeen );
    p->pValues = ABC_ALLOC( int, nVars );
    memset( p->pValues, 0xff, sizeof(int) * nVars );
    p->pReasons = ABC_CALLOC( int, nVars );
    p->pSeen = ABC_CALLOC( unsigned char, nVars );
    Vec_IntFillExtra( p->vPartA, nVars, p->fDual );
    if ( Imc_ProofSeek(pFile, p->ProofOffset, SEEK_SET) )
        goto invalid;
    Read.Buffer = ABC_ALLOC( unsigned char, 65536 );
    Read.pFile = pFile;
    Read.Offset = p->ProofOffset;
    while ( (c = Imc_PrfByte(&Read)) != EOF )
    {
        if ( (nRecords++ & 1023) == 0 && Imc_ManCheckStop(TimeStop) )
            goto finish;
        if ( c == 'd' || c == 'w' || c == 'r' )
        {
            do {
                if ( !Imc_PrfReadId(&Read, &Num) )
                    goto invalid;
            } while ( Num );
            continue;
        }
        if ( c == 'e' )
        {
            // A partial trail is diagnostic only; no proof uses its values.
            if ( !fUnknown ) goto invalid;
            do {
                if ( !Imc_PrfReadNum(&Read, &Num) || Abc_AbsInt(Num) > nVars )
                    goto invalid;
            } while ( Num );
            fUnknown = 0;
            continue;
        }
        if ( c == 's' )
        {
            const char * pStatus;
            int Kind;
            if ( Imc_PrfByte(&Read) != 'U' || Imc_PrfByte(&Read) != 'N' )
                goto invalid;
            Kind = Imc_PrfByte( &Read );
            if ( Kind == 'S' ) pStatus = "ATISFIABLE";
            else if ( Kind == 'K' && fQuery )
            {
                // A conflict-limited query may resume with the same two
                // assumptions. Its learned clauses remain proof ancestors.
                pStatus = "NOWN";
                fQuery = 0;
                fUnknown = 1;
            }
            else goto invalid;
            for ( i = 0; pStatus[i]; i++ )
                if ( Imc_PrfByte(&Read) != pStatus[i] )
                    goto invalid;
            continue;
        }
        if ( c != 'i' && c != 'l' && c != 'q' && c != 'u' )
            goto invalid;
        if ( (c == 'i' || c == 'l') && (!Imc_PrfReadId(&Read, &Id) || !Imc_PrfValidId(p, Id) || Imc_PrfLookup(p, Id)) )
            goto invalid;
        Vec_IntClear( vLits );
        Vec_IntClear( vChain );
        for ( ; ; )
        {
            if ( !Imc_PrfReadNum(&Read, &Num) )
                goto invalid;
            if ( Num == 0 )
                break;
            if ( Abc_AbsInt(Num) > nVars )
                goto invalid;
            Lit = Abc_Var2Lit( Abc_AbsInt(Num)-1, Num < 0 );
            if ( (c == 'q' || c == 'u') && Lit != LitA && Lit != LitB )
                goto invalid;
            Vec_IntPush( vLits, Lit ^ (c == 'u') );
        }
        if ( c == 'q' )
        {
            if ( Vec_IntSize(vLits) != 2 || Vec_IntEntry(vLits, 0) != LitA || Vec_IntEntry(vLits, 1) != LitB )
                goto invalid;
            fQuery = 1;
            fUnknown = 0;
            continue;
        }
        if ( c == 'i' )
        {
            if ( nPending >= Vec_PtrSize(p->vPending) )
                goto invalid;
            pCls = (Imc_Cls_t *)Vec_PtrEntry( p->vPending, nPending );
            if ( pCls == NULL || pCls->nLits != Vec_IntSize(vLits) || memcmp(pCls->pLits, Vec_IntArray(vLits), sizeof(int) * pCls->nLits) )
                goto invalid;
            Vec_PtrFillExtra( p->vClauses, Id + 1, NULL );
            Vec_PtrWriteEntry( p->vClauses, Id, pCls );
            Vec_PtrWriteEntry( p->vPending, nPending++, NULL );
            continue;
        }
        for ( ; ; )
        {
            if ( !Imc_PrfReadId(&Read, &Num) )
                goto invalid;
            if ( Num == 0 )
                break;
            if ( (c == 'l' && Num >= Id) || Imc_PrfLookup(p, Num) == NULL )
                goto invalid;
            Vec_IntPush( vChain, Num );
        }
        if ( c == 'u' )
        {
            if ( !fQuery || nPending != Vec_PtrSize(p->vPending) )
                goto invalid;
            Vec_IntForEachEntry( vLits, Lit, i )
                if ( Abc_Lit2Var(Lit) < Vec_IntSize(p->vGlobal) && Vec_IntEntry(p->vGlobal, Abc_Lit2Var(Lit)) >= 0 )
                    goto invalid;
            fFinal = 1;
            break;
        }
        Vec_PtrFillExtra( p->vClauses, Id + 1, NULL );
        Vec_PtrWriteEntry( p->vClauses, Id, Imc_PrfClause(p, Vec_IntArray(vLits), Vec_IntSize(vLits), -1, -1, Vec_IntArray(vChain), Vec_IntSize(vChain)) );
    }
    if ( !fFinal )
        goto invalid;
    // Trim using only dependencies of the current assumption refutation.
    Vec_IntForEachEntry( vChain, Id, i )
    {
        pCls = Imc_PrfLookup( p, Id );
        if ( pCls->iInter < 0 && !pCls->fUsed )
        {
            pCls->fUsed = 1;
            Vec_IntPush( vUsed, Id );
        }
    }
    Vec_IntForEachEntry( vUsed, Id, i )
    {
        if ( (i & 1023) == 0 && Imc_ManCheckStop(TimeStop) )
            goto finish;
        pCls = Imc_PrfLookup( p, Id );
        for ( k = 0; k < pCls->nHints; k++ )
        {
            Num = pCls->pLits[pCls->nLits + k];
            pNext = Imc_PrfLookup( p, Num );
            if ( pNext->iInter >= 0 || pNext->fUsed )
                continue;
            pNext->fUsed = 1;
            Vec_IntPush( vUsed, Num );
        }
    }
    Vec_IntSort( vUsed, 0 );
    Vec_IntForEachEntry( vUsed, Id, i )
    {
        Vec_Int_t Lits, Chain;
        if ( (i & 255) == 0 && Imc_ManCheckStop(TimeStop) )
            goto finish;
        pCls = Imc_PrfLookup( p, Id );
        if ( pCls->fPartA >= 0 )
            continue;
        Lits.nCap = Lits.nSize = pCls->nLits;
        Lits.pArray = pCls->pLits;
        Chain.nCap = Chain.nSize = pCls->nHints;
        Chain.pArray = pCls->pLits + pCls->nLits;
        pCls->iInter = Imc_PrfReplay( p, &Lits, &Chain );
        if ( pCls->iInter < 0 )
            goto invalid;
    }
    Lit = Imc_PrfReplay( p, vLits, vChain );
    if ( Lit < 0 )
        goto invalid;
    pResult = Imc_PrfExtract( p->pGia, Lit ^ p->fDual );
    goto finish;
invalid:
    Abc_Print( -1, "IMC: Invalid incremental proof record '%c', clause %d, offset %lld.\n", c, Id, (long long)(Read.Offset + Read.Pos) );
finish:
    if ( pResult )
        p->ProofOffset = Read.Offset + Read.Pos;
    else
        p->fFailed = 1;
    ABC_FREE( Read.Buffer );
    Imc_ProofSeek( pFile, 0, SEEK_END );
    // Remove consumed roots even on failure; the remaining roots still
    // belong to this object. A failed stream is permanently rejected.
    for ( i = nPending; i < Vec_PtrSize(p->vPending); i++ )
        Vec_PtrWriteEntry( p->vPending, i - nPending, Vec_PtrEntry(p->vPending, i) );
    Vec_PtrShrink( p->vPending, Vec_PtrSize(p->vPending) - nPending );
    Vec_IntForEachEntry( vUsed, Id, i )
        Imc_PrfLookup(p, Id)->fUsed = 0;
    Vec_IntFree( vLits );
    Vec_IntFree( vChain );
    Vec_IntFree( vUsed );
    return pResult;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
