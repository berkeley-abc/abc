/**CFile****************************************************************

  FileName    [cecCorr3.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [Persistent speculative reduction with lazy updates.]

  Description [New experimental implementation.]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecCorr3.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cecInt.h"
#include "misc/util/utilTruth.h"
#include <limits.h>

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                           DECLARATIONS                           ///
////////////////////////////////////////////////////////////////////////

// Fixed scheduling thresholds, independent of the -C conflict limit.
#define CEC3_HARD_CONFLICTS  10
#define CEC3_DEFER_LIMIT      3

typedef struct Cec3_Que_t_ Cec3_Que_t;
struct Cec3_Que_t_
{
    word * pBits[8];
    int nWords[8], nLevels, nEntries, iWord;
};

typedef struct Cec3_Sig_t_ Cec3_Sig_t;
struct Cec3_Sig_t_
{
    word Signature;
    int Id;
};
typedef struct Cec3_Man_t_ Cec3_Man_t;
typedef struct Cec3_Hash_t_ Cec3_Hash_t;
struct Cec3_Hash_t_
{
    int a, b, Lit;
};
struct Cec3_Man_t_
{
    Gia_Man_t * pAig, * pCore;
    Cec_ParCor_t * pPars;
    Cbs_Man_t * pSat;
    int nObjs, nPis, nRegs, nFrames, nSimFrames, fBase;
    int * pRaw, * pSpec;              // cached literals, indexed by frame * nObjs + object
    int * pPrev;                     // predecessor in the current equivalence ring
    int * pSimRefs;                  // references from true, unrolled candidate cones
    int * pFanStarts;
    Vec_Int_t * vFans;               // AND destinations or next-frame register destinations
    Vec_Int_t * vRemap;              // nonidentity initial-register mappings, frozen per SAT pass
    unsigned char * pPhase, * pActive, * pCandidate;
    unsigned char * pHard;           // 0: cheap/unknown; otherwise 1 + deferrals since the last hard proof
    Vec_Int_t * vActive, * vChanged, * vMembers, * vRoots, * vConstants;
    Cec3_Sig_t * pSort;
    int nSort, nSortCap;
    Vec_Str_t * vProven;             // UNSAT root literals in this core generation
    Vec_Int_t * vSeen;               // root literals already queried in this pass
    int * pClassMark;
    int ClassStamp, SolveStamp, nCoreInitial;
    word * pSims, * pInputs, * pPresence;
    Vec_Int_t * vPresence;
    Vec_Int_t * vProgram;            // dense simulation triples: destination, fanin0, fanin1
    Vec_Wrd_t * vCoreSims;
    Vec_Int_t * vJustify, * vModel, * vJustified;
    int JustifyStamp;
    Cec3_Hash_t * pHash;
    unsigned nHashSize, nHashEntries;
    Cec3_Que_t Update, Sim;
    ABC_INT64_T nUpdates, nSimUpdates, nSat, nReuse, nSplits, nSimSat;
    int nRebuilds, nRounds, nBatches, nUnknown, nReplayFallback, nSimLive, nDense;
    abctime tSrm, tSat, tSim;
};

static int Cec3_Raw( Cec3_Man_t * p, int Id, int f );
static int Cec3_Spec( Cec3_Man_t * p, int Id, int f );

extern int Cbs_ManReadConflictNum( Cbs_Man_t * p );

////////////////////////////////////////////////////////////////////////
///                       FUNCTION DEFINITIONS                       ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Converts clock ticks to seconds for reporting.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static double Cec3_Seconds( abctime Time )
{
    return (double)Time / CLOCKS_PER_SEC;
}

/**Function*************************************************************

  Synopsis    [Draws a 64-bit random word in a fixed order.]

  Description [The high half is drawn before the low half in separate full
  expressions so the random stream does not depend on operand evaluation order.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word Cec3_RandomWord( void )
{
    unsigned High = Gia_ManRandom( 0 );
    unsigned Low = Gia_ManRandom( 0 );
    return ( (word)High << 32 ) | (word)Low;
}


/**Function*************************************************************

  Synopsis    [Allocates a hierarchical bitset queue.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec3_QueStart( Cec3_Que_t * p, int nKeys )
{
    int n = nKeys;
    memset( p, 0, sizeof( *p ) );
    p->iWord = -1;
    do
    {
        n = ( n + 63 ) / 64;
        p->nWords[p->nLevels] = n;
        p->pBits[p->nLevels++] = ABC_CALLOC( word, n );
    } while ( n > 1 );
}
/**Function*************************************************************

  Synopsis    [Clears all pending queue entries.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec3_QueClear( Cec3_Que_t * p )
{
    int i;
    for ( i = 0; i < p->nLevels; i++ )
        memset( p->pBits[i], 0, sizeof( word ) * p->nWords[i] );
    p->nEntries = 0;
    p->iWord = -1;
}
/**Function*************************************************************

  Synopsis    [Releases the queue storage.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec3_QueStop( Cec3_Que_t * p )
{
    int i;
    for ( i = 0; i < p->nLevels; i++ )
        ABC_FREE( p->pBits[i] );
}
/**Function*************************************************************

  Synopsis    [Schedules a key unless it is already pending.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cec3_QuePush( Cec3_Que_t * p, int Key )
{
    int i;
    word Bit = (word)1 << ( Key & 63 );
    if ( p->pBits[0][Key >> 6] & Bit )
        return;
    p->nEntries++;
    if ( p->iWord >= 0 && ( Key >> 6 ) < p->iWord )
        p->iWord = Key >> 6;
    for ( i = 0; i < p->nLevels; i++, Key >>= 6 )
    {
        word Old = p->pBits[i][Key >> 6];
        p->pBits[i][Key >> 6] |= (word)1 << ( Key & 63 );
        if ( Old )
            break;
    }
}
/**Function*************************************************************

  Synopsis    [Removes the smallest pending key.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cec3_QuePop( Cec3_Que_t * p )
{
    int i, Key = 0, Result;
    assert( p->nEntries > 0 );
    if ( p->iWord < 0 )
    {
        for ( i = p->nLevels - 1; i >= 1; i-- )
            Key = 64 * Key + Abc_Tt6FirstBit( p->pBits[i][Key] );
        p->iWord = Key;
    }
    Key = 64 * p->iWord + Abc_Tt6FirstBit( p->pBits[0][p->iWord] );
    Result = Key;
    for ( i = 0; i < p->nLevels; i++, Key >>= 6 )
    {
        p->pBits[i][Key >> 6] &= ~( (word)1 << ( Key & 63 ) );
        if ( p->pBits[i][Key >> 6] )
            break;
        if ( i == 0 )
            p->iWord = -1;
    }
    p->nEntries--;
    return Result;
}

/**Function*************************************************************

  Synopsis    [Hashes two literals using fixed-width unsigned arithmetic.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned Cec3_HashKey( int a, int b, unsigned Mask )
{
    word Key = ( (word)(unsigned)a << 32 ) | (unsigned)b;
    Key ^= Key >> 33;
    Key *= ABC_CONST(0xff51afd7ed558ccd);
    Key ^= Key >> 33;
    return (unsigned)Key & Mask;
}
/**Function*************************************************************

  Synopsis    [Grows and rehashes the speculative AND table.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec3_HashGrow( Cec3_Man_t * p )
{
    unsigned i, Slot, OldSize = p->nHashSize;
    Cec3_Hash_t * pOld = p->pHash;
    assert( OldSize <= UINT_MAX / 2 );
    p->nHashSize = OldSize ? 2 * OldSize : 1024;
    p->pHash = ABC_CALLOC( Cec3_Hash_t, p->nHashSize );
    for ( i = 0; i < OldSize; i++ )
        if ( pOld[i].Lit )
        {
            Slot = Cec3_HashKey( pOld[i].a, pOld[i].b, p->nHashSize - 1 );
            while ( p->pHash[Slot].Lit )
                Slot = ( Slot + 1 ) & ( p->nHashSize - 1 );
            p->pHash[Slot] = pOld[i];
        }
    ABC_FREE( pOld );
}
// Keep the GIA and literal insertion order unchanged, but store the two
// fanins beside the result so a hash hit needs no chain or GIA-node load.
/**Function*************************************************************

  Synopsis    [Finds or creates a speculative AND literal.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cec3_HashAnd( Cec3_Man_t * p, int a, int b )
{
    unsigned Slot;
    if ( a < 2 ) return a ? b : 0;
    if ( b < 2 ) return b ? a : 0;
    if ( a == b ) return a;
    if ( a == ( b ^ 1 ) ) return 0;
    if ( a > b ) ABC_SWAP( int, a, b );
    if ( 2 * (word)p->nHashEntries >= p->nHashSize )
        Cec3_HashGrow( p );
    Slot = Cec3_HashKey( a, b, p->nHashSize - 1 );
    while ( p->pHash[Slot].Lit )
    {
        if ( p->pHash[Slot].a == a && p->pHash[Slot].b == b )
            return p->pHash[Slot].Lit;
        Slot = ( Slot + 1 ) & ( p->nHashSize - 1 );
    }
    p->pHash[Slot].a = a;
    p->pHash[Slot].b = b;
    p->pHash[Slot].Lit = Gia_ManAppendAnd( p->pCore, a, b );
    p->nHashEntries++;
    return p->pHash[Slot].Lit;
}
/**Function*************************************************************

  Synopsis    [Constructs an XOR with a fixed node insertion order.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec3_HashXor( Cec3_Man_t * p, int a, int b )
{
    int Phase = ( a ^ b ) & 1;
    int x = Cec3_HashAnd( p, a & ~1, b | 1 );
    int y = Cec3_HashAnd( p, a | 1, b & ~1 );
    return Cec3_HashAnd( p, x ^ 1, y ^ 1 ) ^ !Phase;
}

/**Function*************************************************************

  Synopsis    [Checks whether an object belongs to a candidate class.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cec3_IsCandidate( Cec3_Man_t * p, int Id )
{
    return Gia_ObjRepr( p->pAig, Id ) != GIA_VOID || Gia_ObjNext( p->pAig, Id ) != 0;
}
/**Function*************************************************************

  Synopsis    [Activates one candidate obligation in a given frame.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec3_Activate( Cec3_Man_t * p, int Id, int f )
{
    int Key = f * p->nObjs + Id;
    if ( !Id || p->pActive[Key] || !Cec3_IsCandidate( p, Id ) )
        return;
    p->pActive[Key] = 1;
    Vec_IntPush( p->vActive, Key );
}
/**Function*************************************************************

  Synopsis    [Activates the obligations affected by an object.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec3_ActivateNode( Cec3_Man_t * p, int Id )
{
    int f;
    if ( p->fBase )
        for ( f = 0; f < p->nFrames; f++ )
            Cec3_Activate( p, Id, f );
    else
        Cec3_Activate( p, Id, p->nFrames );
}
// Partitioning and removal already activate their affected nodes.
/**Function*************************************************************

  Synopsis    [Changes a representative and schedules cache invalidation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec3_SetRepr( Cec3_Man_t * p, int Id, int Repr )
{
    int f, Key;
    if ( Gia_ObjRepr( p->pAig, Id ) == Repr )
        return;
    Gia_ObjSetRepr( p->pAig, Id, Repr );
    p->nSplits++;
    for ( f = 0; f <= p->nFrames; f++ )
    {
        Key = f * p->nObjs + Id;
        if ( p->pSpec[Key] >= 0 )
            Cec3_QuePush( &p->Update, 2 * Key + 1 );
    }

}

/**Function*************************************************************

  Synopsis    [Computes a raw literal from speculative fanins.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec3_ComputeRaw( Cec3_Man_t * p, int Id, int f )
{
    Gia_Obj_t * pObj = Gia_ManObj( p->pAig, Id );
    int a, b;
    if ( !Id )
        return 0;
    if ( Gia_ObjIsAnd( pObj ) )
    {
        a = Cec3_Spec( p, Gia_ObjFaninId0( pObj, Id ), f ) ^ Gia_ObjFaninC0( pObj );
        b = Cec3_Spec( p, Gia_ObjFaninId1( pObj, Id ), f ) ^ Gia_ObjFaninC1( pObj );
        return Cec3_HashAnd( p, a, b );
    }
    if ( Gia_ObjIsPi( p->pAig, pObj ) )
        return Gia_ManCiLit( p->pCore, p->nRegs + f * p->nPis + Gia_ObjCioId( pObj ) );
    assert( Gia_ObjIsRo( p->pAig, pObj ) );
    if ( f == 0 )
        return p->fBase ? 0 : Gia_ManCiLit( p->pCore, Gia_ObjCioId( pObj ) - p->nPis );
    pObj = Gia_ObjRoToRi( p->pAig, pObj );
    return Cec3_Spec( p, Gia_ObjFaninId0p( p->pAig, pObj ), f - 1 ) ^ Gia_ObjFaninC0( pObj );
}
/**Function*************************************************************

  Synopsis    [Returns a cached raw literal, constructing it if needed.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec3_Raw( Cec3_Man_t * p, int Id, int f )
{
    int Key = f * p->nObjs + Id;
    if ( p->pRaw[Key] < 0 )
        p->pRaw[Key] = Cec3_ComputeRaw( p, Id, f );
    return p->pRaw[Key];
}
/**Function*************************************************************

  Synopsis    [Computes a literal with representative substitution.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec3_ComputeSpec( Cec3_Man_t * p, int Id, int f )
{
    int Repr = Gia_ObjRepr( p->pAig, Id );
    if ( Id && Repr != GIA_VOID )
        return Cec3_Spec( p, Repr, f ) ^ p->pPhase[Id] ^ p->pPhase[Repr];
    return Cec3_Raw( p, Id, f );
}
/**Function*************************************************************

  Synopsis    [Returns a cached speculative literal.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec3_Spec( Cec3_Man_t * p, int Id, int f )
{
    int Key = f * p->nObjs + Id;
    if ( p->pSpec[Key] < 0 )
        p->pSpec[Key] = Cec3_ComputeSpec( p, Id, f );
    return p->pSpec[Key];
}
// Propagate invalidation before constructing any roots.  A cached consumer
// always has cached dependencies, so an absent entry needs no propagation.
// Keep activating all affected root endpoints, including base-class members
// and the preceding step-ring edge, even if rebuilding would yield the same
// literal.  Proven immutable core literals remain valid until compaction.
/**Function*************************************************************

  Synopsis    [Invalidates changed literals and their cached consumers.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec3_Invalidate( Cec3_Man_t * p )
{
    int Event, Key, Id, f = 0, Fan, i, Member, nFanouts, * pFanouts;
    int FrameBase = 0, FrameLimit = p->nObjs;
    while ( p->Update.nEntries )
    {
        Event = Cec3_QuePop( &p->Update );
        Key = Event >> 1;
        if ( Key < FrameBase || Key >= FrameLimit )
        {
            f = Key / p->nObjs;
            FrameBase = f * p->nObjs;
            FrameLimit = FrameBase + p->nObjs;
        }
        Id = Key - FrameBase;
        assert( ( ( Event & 1 ) ? p->pSpec[Key] : p->pRaw[Key] ) >= 0 );
        p->nUpdates++;
        if ( !( Event & 1 ) )
        {
            p->pRaw[Key] = -1;
            if ( Gia_ObjRepr( p->pAig, Id ) == GIA_VOID && p->pSpec[Key] >= 0 )
                Cec3_QuePush( &p->Update, Event + 1 );
            if ( p->fBase && f < p->nFrames )
            {
                Cec3_Activate( p, Id, f );
                if ( Gia_ObjIsHead( p->pAig, Id ) )
                    Gia_ClassForEachObj1( p->pAig, Id, Member )
                        Cec3_Activate( p, Member, f );
            }
            else if ( !p->fBase && f == p->nFrames )
            {
                Cec3_Activate( p, Id, f );
                Cec3_Activate( p, p->pPrev[Id], f );
            }
            continue;
        }
        p->pSpec[Key] = -1;
        if ( Gia_ObjIsHead( p->pAig, Id ) )
            Gia_ClassForEachObj1( p->pAig, Id, Member )
                if ( p->pSpec[f * p->nObjs + Member] >= 0 )
                    Cec3_QuePush( &p->Update, 2 * ( f * p->nObjs + Member ) + 1 );
        nFanouts = p->pFanStarts[Id + 1] - p->pFanStarts[Id];
        pFanouts = Vec_IntArray( p->vFans ) + p->pFanStarts[Id];
        for ( i = 0; i < nFanouts; i++ )
        {
            Fan = FrameBase + pFanouts[i];
            if ( Fan < ( p->nFrames + 1 ) * p->nObjs && p->pRaw[Fan] >= 0 )
                Cec3_QuePush( &p->Update, 2 * Fan );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Orders signatures and breaks ties by object ID.]

  Description [Object IDs give a total order independent of qsort stability.]

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec3_SortCompare( const void * a, const void * b )
{
    const Cec3_Sig_t *x = (const Cec3_Sig_t *)a, *y = (const Cec3_Sig_t *)b;
    if ( x->Signature != y->Signature )
        return x->Signature > y->Signature ? 1 : -1;
    return ( x->Id > y->Id ) - ( x->Id < y->Id );
}
/**Function*************************************************************

  Synopsis    [Appends an object and its simulation signature.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec3_SortPush( Cec3_Man_t * p, word Signature, int Id )
{
    if ( p->nSort == p->nSortCap )
    {
        p->nSortCap = p->nSortCap ? 2 * p->nSortCap : 100;
        p->pSort = ABC_REALLOC( Cec3_Sig_t, p->pSort, p->nSortCap );
    }
    p->pSort[p->nSort].Signature = Signature;
    p->pSort[p->nSort++].Id = Id;
}
/**Function*************************************************************

  Synopsis    [Returns a phase-normalized simulation signature.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word Cec3_Signature( Cec3_Man_t * p, int Id, int f )
{
    word Val = p->pSims[f * p->nObjs + Id];
    return p->pPhase[Id] ? ~Val : Val;
}
// All current candidates, in every replay frame, are simulation roots.
// Refinement only removes roots.  Reference-counting their TRUE unrolled
// fanins therefore safely retires values that can never be read again.
// This is deliberately independent of the current SRM active frontier.
/**Function*************************************************************

  Synopsis    [Releases one reference to an unrolled simulation value.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec3_SimDeref( Cec3_Man_t * p, int Key )
{
    assert( p->pSimRefs[Key] > 0 );
    if ( --p->pSimRefs[Key] == 0 )
    {
        p->nSimLive--;
        Vec_IntPush( p->vMembers, Key );
    }
}
/**Function*************************************************************

  Synopsis    [Retires simulation cones no longer used by candidates.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec3_RetireCandidate( Cec3_Man_t * p, int Id )
{
    int f, Key;
    if ( !p->pCandidate[Id] || Cec3_IsCandidate( p, Id ) )
        return;
    p->pCandidate[Id] = 0;
    Vec_IntClear( p->vMembers );
    for ( f = 0; f < p->nSimFrames; f++ )
        Cec3_SimDeref( p, f * p->nObjs + Id );
    while ( Vec_IntSize( p->vMembers ) )
    {
        Gia_Obj_t * pObj;
        Key = Vec_IntPop( p->vMembers );
        f = Key / p->nObjs;
        Id = Key % p->nObjs;
        pObj = Gia_ManObj( p->pAig, Id );
        if ( Gia_ObjIsAnd( pObj ) )
        {
            Cec3_SimDeref( p, f * p->nObjs + Gia_ObjFaninId0( pObj, Id ) );
            Cec3_SimDeref( p, f * p->nObjs + Gia_ObjFaninId1( pObj, Id ) );
        }
        else if ( Gia_ObjIsRo( p->pAig, pObj ) && f )
        {
            pObj = Gia_ObjRoToRi( p->pAig, pObj );
            Cec3_SimDeref( p, ( f - 1 ) * p->nObjs + Gia_ObjFaninId0p( p->pAig, pObj ) );
        }
    }
}
// Install a partition of the members in pSort, sorted by signature and ID.
// A split reports its changes directly to the SRM updater.
/**Function*************************************************************

  Synopsis    [Installs refined equivalence classes in a fixed order.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec3_Partition( Cec3_Man_t * p )
{
    int i, j, k, Id, Head, Prev, Size = p->nSort;
    Cec3_Sig_t * pSort = p->pSort;
    qsort( pSort, Size, sizeof( Cec3_Sig_t ), Cec3_SortCompare );
    for ( i = 0; i < Size; i++ )
    {
        Id = pSort[i].Id;
        Cec3_ActivateNode( p, Id );
    }
    for ( i = 0; i < Size; i = j )
    {
        for ( j = i + 1; j < Size && pSort[j].Signature == pSort[i].Signature; j++ )
        {
        }
        Head = pSort[i].Id;
        Prev = 0;
        for ( k = i; k < j; k++ )
        {
            Id = pSort[k].Id;
            Cec3_SetRepr( p, Id, k == i ? GIA_VOID : Head );
            Gia_ObjSetNext( p->pAig, Id, k + 1 < j ? pSort[k + 1].Id : 0 );
            p->pPrev[Id] = Prev;
            Prev = Id;
        }
        if ( j - i > 1 )
            p->pPrev[Head] = Prev;
    }
    // Only a singleton can lose its last candidate reference.
    for ( i = 0; i < Size; i++ )
        if ( ( !i || pSort[i - 1].Signature != pSort[i].Signature ) &&
             ( i + 1 == Size || pSort[i + 1].Signature != pSort[i].Signature ) )
            Cec3_RetireCandidate( p, pSort[i].Id );
}
/**Function*************************************************************

  Synopsis    [Splits a class whose simulation signatures differ.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec3_RefineClass( Cec3_Man_t * p, int Head, int f )
{
    int Id;
    word First = Cec3_Signature( p, Head, f );
    Gia_ClassForEachObj( p->pAig, Head, Id )
        if ( Cec3_Signature( p, Id, f ) != First )
            break;
    if ( !Id )
        return;
    p->nSort = 0;
    Gia_ClassForEachObj( p->pAig, Head, Id )
        Cec3_SortPush( p, Cec3_Signature( p, Id, f ), Id );
    Cec3_Partition( p );
}
/**Function*************************************************************

  Synopsis    [Refines the classes affected by counterexample replay.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec3_Refine( Cec3_Man_t * p )
{
    int i = 0, j, k, Key, Id, Head, f, FrameBase, FrameLimit;
    while ( i < Vec_IntSize( p->vChanged ) )
    {
        f = Vec_IntEntry( p->vChanged, i ) / p->nObjs;
        FrameBase = f * p->nObjs;
        FrameLimit = FrameBase + p->nObjs;
        Vec_IntClear( p->vRoots );
        Vec_IntClear( p->vConstants );
        if ( p->ClassStamp == INT_MAX )
        {
            memset( p->pClassMark, 0, sizeof(int) * p->nObjs );
            p->ClassStamp = 0;
        }
        p->ClassStamp++;
        for ( j = i; j < Vec_IntSize( p->vChanged ); j++ )
        {
            Key = Vec_IntEntry( p->vChanged, j );
            if ( Key >= FrameLimit )
                break;
            Id = Key - FrameBase;
            if ( Gia_ObjIsConst( p->pAig, Id ) )
            {
                if ( Cec3_Signature( p, Id, f ) )
                    Vec_IntPush( p->vConstants, Id );
                continue;
            }
            Head = Gia_ObjRepr( p->pAig, Id );
            if ( Head == GIA_VOID )
                Head = Id;
            if ( !Gia_ObjIsHead( p->pAig, Head ) || p->pClassMark[Head] == p->ClassStamp )
                continue;
            p->pClassMark[Head] = p->ClassStamp;
            Vec_IntPush( p->vRoots, Head );
        }
        Vec_IntForEachEntry( p->vRoots, Head, k )
            Cec3_RefineClass( p, Head, f );
        p->nSort = 0;
        // Only disproved constants enter the new nonconstant classes.
        Vec_IntForEachEntry( p->vConstants, Id, k )
            Cec3_SortPush( p, Cec3_Signature( p, Id, f ), Id );
        if ( p->nSort )
            Cec3_Partition( p );
        i = j;
    }
    Vec_IntClear( p->vChanged );
}
/**Function*************************************************************

  Synopsis    [Removes an unresolved object from its candidate class.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec3_Remove( Cec3_Man_t * p, int Id )
{
    int Head, Member;
    if ( !Id || !Cec3_IsCandidate( p, Id ) )
        return;
    Head = Gia_ObjRepr( p->pAig, Id );
    if ( Head == GIA_VOID )
        Head = Id;
    p->nSort = 0;
    if ( Head )
        Gia_ClassForEachObj( p->pAig, Head, Member )
            if ( Member != Id )
                Cec3_SortPush( p, 0, Member );
    Cec3_SetRepr( p, Id, GIA_VOID );
    Gia_ObjSetNext( p->pAig, Id, 0 );
    p->pPrev[Id] = 0;
    Cec3_ActivateNode( p, Id );
    if ( p->nSort )
        Cec3_Partition( p );
    Cec3_RetireCandidate( p, Id );
}

/**Function*************************************************************

  Synopsis    [Computes one unrolled simulation value.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word Cec3_SimValue( Cec3_Man_t * p, int Id, int f )
{
    Gia_Obj_t * pObj = Gia_ManObj( p->pAig, Id );
    word * v = p->pSims + f * p->nObjs;
    if ( !Id )
        return 0;
    if ( Gia_ObjIsPi( p->pAig, pObj ) )
        return p->pInputs[p->nRegs + f * p->nPis + Gia_ObjCioId( pObj )] & ~(word)1;
    if ( Gia_ObjIsRo( p->pAig, pObj ) )
    {
        if ( !f )
            return p->pInputs[Gia_ObjCioId( pObj ) - p->nPis] & ~(word)1;
        pObj = Gia_ObjRoToRi( p->pAig, pObj );
        return ( p->pSims[( f - 1 ) * p->nObjs + Gia_ObjFaninId0p( p->pAig, pObj )] ^
                 ( Gia_ObjFaninC0( pObj ) ? ~(word)0 : 0 ) ) &
               ~(word)1;
    }
    assert( Gia_ObjIsAnd( pObj ) );
    return ( v[Gia_ObjFaninId0( pObj, Id )] ^ ( Gia_ObjFaninC0( pObj ) ? ~(word)0 : 0 ) ) &
           ( v[Gia_ObjFaninId1( pObj, Id )] ^ ( Gia_ObjFaninC1( pObj ) ? ~(word)0 : 0 ) );
}
/**Function*************************************************************

  Synopsis    [Propagates changed values and refines candidate classes.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec3_Simulate( Cec3_Man_t * p )
{
    int Key, Id, f = 0, Fan, i, nFanouts, * pFanouts, nEvents = 0;
    int FrameBase = 0, FrameLimit = p->nObjs;
    int nDenseThreshold = Abc_MaxInt( 1000, p->nSimLive / 20 );
    if ( Vec_IntSize( p->vProgram ) / 3 > p->nSimLive + p->nSimLive / 4 )
    {
        int Read, Write = 0;
        for ( Read = 0; Read < Vec_IntSize( p->vProgram ); Read += 3 )
            if ( p->pSimRefs[Vec_IntEntry( p->vProgram, Read )] )
            {
                for ( i = 0; i < 3; i++ )
                    Vec_IntWriteEntry( p->vProgram, Write + i, Vec_IntEntry( p->vProgram, Read + i ) );
                Write += 3;
            }
        Vec_IntShrink( p->vProgram, Write );
    }
    while ( p->Sim.nEntries )
    {
        word New;
        Key = Cec3_QuePop( &p->Sim );
        if ( Key < FrameBase || Key >= FrameLimit )
        {
            f = Key / p->nObjs;
            FrameBase = f * p->nObjs;
            FrameLimit = FrameBase + p->nObjs;
        }
        Id = Key - FrameBase;
        New = Cec3_SimValue( p, Id, f );
        p->nSimUpdates++;
        nEvents++;
        if ( p->pSims[Key] == New )
            continue;
        p->pSims[Key] = New;
        if ( p->pCandidate[Id] )
            Vec_IntPush( p->vChanged, Key );
        nFanouts = p->pFanStarts[Id + 1] - p->pFanStarts[Id];
        pFanouts = Vec_IntArray( p->vFans ) + p->pFanStarts[Id];
        for ( i = 0; i < nFanouts; i++ )
        {
            Fan = FrameBase + pFanouts[i];
            if ( Fan < p->nSimFrames * p->nObjs && p->pSimRefs[Fan] )
                Cec3_QuePush( &p->Sim, Fan );
        }
        // For a broad change, a linear sweep is cheaper than continuing
        // event propagation.  All lower keys have already settled.
        if ( nEvents > nDenseThreshold )
        {
            int Lo = 0, Hi = Vec_IntSize( p->vProgram ) / 3, * pCode = Vec_IntArray( p->vProgram );
            p->nDense++;
            Cec3_QueClear( &p->Sim );
            while ( Lo < Hi )
            {
                int Mid = Lo + ( Hi - Lo ) / 2;
                if ( pCode[3 * Mid] <= Key )
                    Lo = Mid + 1;
                else
                    Hi = Mid;
            }
            for ( i = 3 * Lo; i < Vec_IntSize( p->vProgram ); i += 3 )
            {
                int a = pCode[i + 1], b = pCode[i + 2];
                Key = pCode[i];
                if ( !p->pSimRefs[Key] )
                    continue;
                if ( a < 0 )
                    New = p->pInputs[-a - 1] & ~(word)1;
                else if ( b < 0 )
                    New = ( p->pSims[a >> 1] ^ -(word)( a & 1 ) ) & ~(word)1;
                else
                    New = ( p->pSims[a >> 1] ^ -(word)( a & 1 ) ) & ( p->pSims[b >> 1] ^ -(word)( b & 1 ) );
                p->nSimUpdates++;
                if ( p->pSims[Key] == New )
                    continue;
                p->pSims[Key] = New;
                if ( Key >= FrameLimit )
                {
                    FrameBase = Key / p->nObjs * p->nObjs;
                    FrameLimit = FrameBase + p->nObjs;
                }
                Id = Key - FrameBase;
                if ( p->pCandidate[Id] )
                    Vec_IntPush( p->vChanged, Key );
            }
            break;
        }
    }
    Cec3_Refine( p );
}
/**Function*************************************************************

  Synopsis    [Updates an input pattern and schedules its simulation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Cec3_SetInput( Cec3_Man_t * p, int Var, word Value )
{
    int f, Id;
    Value &= ~(word)1;
    if ( p->pInputs[Var] == Value )
        return;
    p->pInputs[Var] = Value;
    if ( Var < p->nRegs )
    {
        f = 0;
        Id = Gia_ObjId( p->pAig, Gia_ManRo( p->pAig, Var ) );
    }
    else
    {
        f = ( Var - p->nRegs ) / p->nPis;
        Id = Gia_ObjId( p->pAig, Gia_ManPi( p->pAig, ( Var - p->nRegs ) % p->nPis ) );
    }
    if ( p->pSimRefs[f * p->nObjs + Id] )
        Cec3_QuePush( &p->Sim, f * p->nObjs + Id );
}
/**Function*************************************************************

  Synopsis    [Applies the frozen initial-register mapping.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec3_Remap( Cec3_Man_t * p )
{
    int i, Var, Repr;
    Vec_IntForEachEntryDouble( p->vRemap, Var, Repr, i )
        Cec3_SetInput( p, Var, Repr < 0 ? 0 : p->pInputs[Repr] );
}
/**Function*************************************************************

  Synopsis    [Replays a packed counterexample batch and clears its masks.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec3_Flush( Cec3_Man_t * p )
{
    int Var, i;
    p->nBatches++;
    Cec3_Remap( p );
    Cec3_Simulate( p );
    Vec_IntForEachEntry( p->vPresence, Var, i )
        p->pPresence[Var] = 0;
    Vec_IntClear( p->vPresence );
}
/**Function*************************************************************

  Synopsis    [Packs and replays SAT counterexamples.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec3_Resimulate( Cec3_Man_t * p, Vec_Int_t * vStore )
{
    int Start = 0, Size, i, Bit, Lit, Var;
    Gia_Obj_t * pObj;
    // Every cube in this pass uses the same speculative initial state.
    // Keep that mapping even when earlier replay batches split classes.
    Vec_IntClear( p->vRemap );
    Gia_ManForEachRo( p->pAig, pObj, i )
    {
        int Repr = Gia_ObjRepr( p->pAig, Gia_ObjId( p->pAig, pObj ) );
        int Map = p->fBase || Repr == 0 ? -1
                  : Repr == GIA_VOID    ? i
                                        : Gia_ObjCioId( Gia_ManObj( p->pAig, Repr ) ) - p->nPis;
        if ( Map != i )
            Vec_IntPushTwo( p->vRemap, i, Map );
    }
    while ( Start < Vec_IntSize( vStore ) )
    {
        word Available = ~(word)1;
        Size = Vec_IntEntry( vStore, Start++ );
        // Reject incompatible slots for all 63 patterns at once.  Choosing
        // the first remaining bit preserves the original packing order.
        for ( i = 0; i < Size && Available; i++ )
        {
            Lit = Vec_IntEntry( vStore, Start + i );
            Var = Abc_Lit2Var( Lit );
            Available &= ~( p->pPresence[Var] & ( p->pInputs[Var] ^ -(word)!Abc_LitIsCompl( Lit ) ) );
        }
        if ( !Available )
        {
            Cec3_Flush( p );
            Start--;
            continue;
        }
        Bit = Abc_Tt6FirstBit( Available );
        for ( i = 0; i < Size; i++ )
        {
            word Mask = (word)1 << Bit, Value;
            Lit = Vec_IntEntry( vStore, Start + i );
            Var = Abc_Lit2Var( Lit );
            if ( !p->pPresence[Var] )
                Vec_IntPush( p->vPresence, Var );
            p->pPresence[Var] |= Mask;
            Value = Abc_LitIsCompl( Lit ) ? p->pInputs[Var] & ~Mask : p->pInputs[Var] | Mask;
            Cec3_SetInput( p, Var, Value );
        }
        Start += Size;
    }
    Cec3_Flush( p );
}

/**Function*************************************************************

  Synopsis    [Creates a core and resets caches tied to the old core.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec3_CoreStart( Cec3_Man_t * p )
{
    int i, f;
    if ( p->pSat )
        Cbs_ManStop( p->pSat );
    if ( p->pCore )
        Gia_ManStop( p->pCore );
    p->pSat = NULL;
    p->pCore = Gia_ManStart( Abc_MaxInt( 1000, p->nObjs ) );
    if ( p->pHash )
        memset( p->pHash, 0, sizeof(Cec3_Hash_t) * (size_t)p->nHashSize );
    p->nHashEntries = 0;
    for ( i = 0; i < p->nRegs + ( p->nFrames + 1 ) * p->nPis; i++ )
        Gia_ManAppendCi( p->pCore );
    memset( p->pRaw, 255, sizeof( int ) * ( p->nFrames + 1 ) * p->nObjs );
    memset( p->pSpec, 255, sizeof( int ) * ( p->nFrames + 1 ) * p->nObjs );
    Cec3_QueClear( &p->Update );
    Vec_StrClear( p->vProven );
    Vec_IntClear( p->vSeen );
    Vec_WrdClear( p->vCoreSims );
    Vec_IntClear( p->vJustified );
    for ( f = 0; f <= p->nFrames; f++ )
        p->pRaw[f * p->nObjs] = p->pSpec[f * p->nObjs] = 0;
    for ( i = 1; i < p->nObjs; i++ )
        if ( Cec3_IsCandidate( p, i ) )
            Cec3_ActivateNode( p, i );
    p->nCoreInitial = 0;
    p->nRebuilds++;
}
/**Function*************************************************************

  Synopsis    [Initializes the base-case or induction-step manager.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static Cec3_Man_t * Cec3_Start( Gia_Man_t * pAig, Cec_ParCor_t * pPars, int fBase )
{
    Cec3_Man_t * p = ABC_CALLOC( Cec3_Man_t, 1 );
    Gia_Obj_t * pObj;
    int i, f, Id, Prev, nKeys;
    p->pAig = pAig;
    p->pPars = pPars;
    p->fBase = fBase;
    p->nObjs = Gia_ManObjNum( pAig );
    p->nPis = Gia_ManPiNum( pAig );
    p->nRegs = Gia_ManRegNum( pAig );
    p->nFrames = pPars->nFrames;
    p->nSimFrames = p->nFrames + ( fBase ? 1 : 2 );
    nKeys = ( p->nFrames + 1 ) * p->nObjs;
    p->pRaw = ABC_ALLOC( int, nKeys );
    p->pSpec = ABC_ALLOC( int, nKeys );
    p->pPrev = ABC_CALLOC( int, p->nObjs );
    p->pPhase = ABC_CALLOC( unsigned char, p->nObjs );
    p->vRemap = Vec_IntAlloc( 100 );
    p->pActive = ABC_CALLOC( unsigned char, nKeys );
    p->pHard = ABC_CALLOC( unsigned char, nKeys );
    p->pClassMark = ABC_CALLOC( int, p->nObjs );
    p->pCandidate = ABC_CALLOC( unsigned char, p->nObjs );
    p->pFanStarts = ABC_ALLOC( int, p->nObjs + 1 );
    p->vFans = Vec_IntAlloc( 2 * Gia_ManAndNum( pAig ) + p->nRegs );
    for ( Id = 0; Id < p->nObjs; Id++ )
    {
        int Fan, k;
        p->pFanStarts[Id] = Vec_IntSize( p->vFans );
        Gia_ObjForEachFanoutStaticId( pAig, Id, Fan, k )
        {
            Gia_Obj_t * pFan = Gia_ManObj( pAig, Fan );
            if ( Gia_ObjIsAnd( pFan ) )
                Vec_IntPush( p->vFans, Fan );
            else if ( Gia_ObjIsRi( pAig, pFan ) )
                Vec_IntPush( p->vFans, p->nObjs + Gia_ObjRiToRoId( pAig, Fan ) );
        }
    }
    p->pFanStarts[p->nObjs] = Vec_IntSize( p->vFans );
    p->pSimRefs = ABC_CALLOC( int, (size_t)p->nSimFrames * p->nObjs );
    p->vActive = Vec_IntAlloc( 1000 );
    p->vChanged = Vec_IntAlloc( 1000 );
    p->vMembers = Vec_IntAlloc( 100 );
    p->vRoots = Vec_IntAlloc( 100 );
    p->vConstants = Vec_IntAlloc( 100 );
    p->vProven = Vec_StrAlloc( 1000 );
    p->vSeen = Vec_IntAlloc( 1000 );
    p->vPresence = Vec_IntAlloc( 1000 );
    p->vProgram = Vec_IntAlloc( 1000 );
    p->vCoreSims = Vec_WrdAlloc( 1000 );
    p->vJustify = Vec_IntAlloc( 1000 );
    p->vModel = Vec_IntAlloc( 1000 );
    p->vJustified = Vec_IntAlloc( 1000 );
    p->pSims = ABC_CALLOC( word, (size_t)p->nSimFrames * p->nObjs );
    p->pInputs = ABC_CALLOC( word, p->nRegs + p->nSimFrames * p->nPis );
    p->pPresence = ABC_CALLOC( word, p->nRegs + p->nSimFrames * p->nPis );
    Cec3_QueStart( &p->Update, 2 * nKeys );
    Cec3_QueStart( &p->Sim, p->nSimFrames * p->nObjs );
    Gia_ManSetPhase( pAig );
    Gia_ManForEachObj( pAig, pObj, i )
        p->pPhase[i] = pObj->fPhase;
    for ( i = 1; i < p->nObjs; i++ )
        if ( ( p->pCandidate[i] = Cec3_IsCandidate( p, i ) ) )
            for ( f = 0; f < p->nSimFrames; f++ )
                p->pSimRefs[f * p->nObjs + i]++;
    for ( f = p->nSimFrames - 1; f >= 0; f-- )
        for ( i = p->nObjs - 1; i > 0; i-- )
        {
            if ( !p->pSimRefs[f * p->nObjs + i] )
                continue;
            pObj = Gia_ManObj( pAig, i );
            if ( Gia_ObjIsAnd( pObj ) )
            {
                p->pSimRefs[f * p->nObjs + Gia_ObjFaninId0( pObj, i )]++;
                p->pSimRefs[f * p->nObjs + Gia_ObjFaninId1( pObj, i )]++;
            }
            else if ( Gia_ObjIsRo( pAig, pObj ) && f )
            {
                pObj = Gia_ObjRoToRi( pAig, pObj );
                p->pSimRefs[( f - 1 ) * p->nObjs + Gia_ObjFaninId0p( pAig, pObj )]++;
            }
        }
    Gia_ManForEachClass( pAig, i )
    {
        Prev = 0;
        Gia_ClassForEachObj( pAig, i, Id )
        {
            p->pPrev[Id] = Prev;
            Prev = Id;
        }
        p->pPrev[i] = Prev;
    }
    for ( i = 0; i < p->nSimFrames * p->nObjs; i++ )
        p->nSimLive += p->pSimRefs[i] != 0;
    Cec3_CoreStart( p );
    for ( i = p->nRegs; i < p->nRegs + p->nSimFrames * p->nPis; i++ )
        p->pInputs[i] = Cec3_RandomWord() & ~(word)1;
    for ( f = 0; f < p->nSimFrames; f++ )
        Gia_ManForEachObj1( pAig, pObj, i )
        {
            if ( Gia_ObjIsCo( pObj ) || !p->pSimRefs[f * p->nObjs + i] )
                continue;
            {
                int a, b;
                if ( Gia_ObjIsAnd( pObj ) )
                {
                    a = 2 * ( f * p->nObjs + Gia_ObjFaninId0( pObj, i ) ) + Gia_ObjFaninC0( pObj );
                    b = 2 * ( f * p->nObjs + Gia_ObjFaninId1( pObj, i ) ) + Gia_ObjFaninC1( pObj );
                }
                else if ( Gia_ObjIsPi( pAig, pObj ) )
                    a = -( p->nRegs + f * p->nPis + Gia_ObjCioId( pObj ) + 1 ), b = 0;
                else if ( !f )
                    a = -( Gia_ObjCioId( pObj ) - p->nPis + 1 ), b = 0;
                else
                {
                    Gia_Obj_t * pRi = Gia_ObjRoToRi( pAig, pObj );
                    a = 2 * ( ( f - 1 ) * p->nObjs + Gia_ObjFaninId0p( pAig, pRi ) ) + Gia_ObjFaninC0( pRi );
                    b = -1;
                }
                Vec_IntPushThree( p->vProgram, f * p->nObjs + i, a, b );
            }
            p->pSims[f * p->nObjs + i] = Cec3_SimValue( p, i, f );
            if ( Cec3_IsCandidate( p, i ) )
                Vec_IntPush( p->vChanged, f * p->nObjs + i );
        }
    Cec3_Refine( p );
    return p;
}
/**Function*************************************************************

  Synopsis    [Releases the correspondence manager and its core.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec3_Stop( Cec3_Man_t * p )
{
    if ( p->pSat )
        Cbs_ManStop( p->pSat );
    Gia_ManStop( p->pCore );
    ABC_FREE( p->pRaw );
    ABC_FREE( p->pSpec );
    ABC_FREE( p->pPrev );
    ABC_FREE( p->pPhase );
    ABC_FREE( p->pActive );
    ABC_FREE( p->pHard );
    ABC_FREE( p->pClassMark );
    ABC_FREE( p->pSims );
    ABC_FREE( p->pInputs );
    ABC_FREE( p->pPresence );
    ABC_FREE( p->pSimRefs );
    ABC_FREE( p->pCandidate );
    ABC_FREE( p->pFanStarts );
    Vec_IntFree( p->vFans );
    Vec_IntFree( p->vRemap );
    ABC_FREE( p->pHash );
    Vec_IntFree( p->vProgram );
    Vec_WrdFree( p->vCoreSims );
    Vec_IntFree( p->vJustify );
    Vec_IntFree( p->vModel );
    Vec_IntFree( p->vJustified );
    Vec_IntFree( p->vActive );
    Vec_IntFree( p->vChanged );
    Vec_IntFree( p->vMembers );
    Vec_IntFree( p->vRoots );
    Vec_IntFree( p->vConstants );
    ABC_FREE( p->pSort );
    Vec_StrFree( p->vProven );
    Vec_IntFree( p->vSeen );
    Vec_IntFree( p->vPresence );
    Cec3_QueStop( &p->Update );
    Cec3_QueStop( &p->Sim );
    ABC_FREE( p );
}
/**Function*************************************************************

  Synopsis    [Constructs one candidate mismatch obligation.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec3_Root( Cec3_Man_t * p, int Key, int * pTarget )
{
    int Id = Key % p->nObjs, f = Key / p->nObjs, Repr = Gia_ObjRepr( p->pAig, Id ), Next, a, b;
    *pTarget = Id;
    if ( p->fBase )
    {
        if ( Repr == GIA_VOID )
            return 0;
        a = Repr ? Cec3_Raw( p, Repr, f ) ^ p->pPhase[Repr] : 0;
        b = Cec3_Raw( p, Id, f ) ^ p->pPhase[Id];
        return Cec3_HashXor( p, a, b );
    }
    if ( Repr == 0 )
        return Cec3_Raw( p, Id, f ) ^ p->pPhase[Id];
    Next = Gia_ObjNext( p->pAig, Id );
    if ( !Next )
        Next = Repr;
    if ( Next == GIA_VOID )
        return 0;
    *pTarget = Next;
    a = Cec3_Raw( p, Id, f ) ^ p->pPhase[Id];
    b = Cec3_Raw( p, Next, f ) ^ p->pPhase[Next];
    return Cec3_HashAnd( p, a, b ^ 1 );
}
// Immutable core nodes need random simulation only once.  A witnessed
// root is already SAT; justify that witness to a sparse input cube rather
// than asking the SAT solver to rediscover it.
/**Function*************************************************************

  Synopsis    [Simulates newly appended speculative core nodes.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec3_CoreSimulate( Cec3_Man_t * p )
{
    int Id;
    for ( Id = Vec_WrdSize( p->vCoreSims ); Id < Gia_ManObjNum( p->pCore ); Id++ )
    {
        Gia_Obj_t * pObj = Gia_ManObj( p->pCore, Id );
        word Value;
        if ( !Id )
            Value = 0;
        else if ( Gia_ObjIsCi( pObj ) )
            Value = Cec3_RandomWord();
        else
            Value = ( Vec_WrdEntry( p->vCoreSims, Gia_ObjFaninId0( pObj, Id ) ) ^ -(word)Gia_ObjFaninC0( pObj ) ) &
                    ( Vec_WrdEntry( p->vCoreSims, Gia_ObjFaninId1( pObj, Id ) ) ^ -(word)Gia_ObjFaninC1( pObj ) );
        Vec_WrdPush( p->vCoreSims, Value );
    }
    Vec_IntFillExtra( p->vJustified, Gia_ManObjNum( p->pCore ), 0 );
}
/**Function*************************************************************

  Synopsis    [Justifies a simulated SAT witness to a sparse input cube.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec3_CoreWitness( Cec3_Man_t * p, int Lit )
{
    word Value = Vec_WrdEntry( p->vCoreSims, Abc_Lit2Var( Lit ) ) ^ -(word)Abc_LitIsCompl( Lit );
    int Bit, Id;
    if ( !Value )
        return 0;
    Bit = Abc_Tt6FirstBit( Value );
    if ( p->JustifyStamp == INT_MAX )
    {
        Vec_IntFill( p->vJustified, Vec_IntSize( p->vJustified ), 0 );
        p->JustifyStamp = 0;
    }
    p->JustifyStamp++;
    Vec_IntClear( p->vJustify );
    Vec_IntClear( p->vModel );
    Vec_IntPush( p->vJustify, Abc_Lit2Var( Lit ) );
    while ( Vec_IntSize( p->vJustify ) )
    {
        Gia_Obj_t * pObj;
        int a, b, Val;
        Id = Vec_IntPop( p->vJustify );
        if ( !Id || Vec_IntEntry( p->vJustified, Id ) == p->JustifyStamp )
            continue;
        Vec_IntWriteEntry( p->vJustified, Id, p->JustifyStamp );
        pObj = Gia_ManObj( p->pCore, Id );
        Val = ( Vec_WrdEntry( p->vCoreSims, Id ) >> Bit ) & 1;
        if ( Gia_ObjIsCi( pObj ) )
        {
            Vec_IntPush( p->vModel, Abc_Var2Lit( Gia_ObjCioId( pObj ), !Val ) );
            continue;
        }
        a = Gia_ObjFaninId0( pObj, Id );
        b = Gia_ObjFaninId1( pObj, Id );
        if ( Val )
        {
            Vec_IntPush( p->vJustify, a );
            Vec_IntPush( p->vJustify, b );
        }
        else if ( !( ( ( Vec_WrdEntry( p->vCoreSims, a ) >> Bit ) & 1 ) ^ Gia_ObjFaninC0( pObj ) ) )
            Vec_IntPush( p->vJustify, a );
        else
            Vec_IntPush( p->vJustify, b );
    }
    p->nSimSat++;
    return 1;
}
/**Function*************************************************************

  Synopsis    [Refines candidates until all remaining obligations are proved.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec3_Run( Cec3_Man_t * p )
{
    Vec_Int_t * vWork = Vec_IntAlloc( 1000 ), * vLits = Vec_IntAlloc( 1000 ), * vTargets = Vec_IntAlloc( 1000 );
    Vec_Int_t * vStore = Vec_IntAlloc( 1000 ), * vFail = Vec_IntAlloc( 100 ), * vDefer = Vec_IntAlloc( 100 );
    int i, Key, Lit, Target, Status, Pass, n, nItems, fOk = 1;
    ABC_INT64_T nDeferred = 0;
    abctime clk;
    for ( p->nRounds = 0; p->nRounds < 100000; p->nRounds++ )
    {
        ABC_INT64_T nSplitsBefore = p->nSplits;
        if ( p->pPars->pFunc && ( (int ( * )( void * ))p->pPars->pFunc )( p->pPars->pData ) )
        {
            fOk = 0;
            break;
        }
        clk = Abc_Clock();
        if ( p->nCoreInitial && Gia_ManObjNum( p->pCore ) > (ABC_INT64_T)4 * p->nCoreInitial )
            Cec3_CoreStart( p );
        Cec3_Invalidate( p );
        if ( !Vec_IntSize( p->vActive ) )
            break;
        ABC_SWAP( Vec_Int_t *, vWork, p->vActive );
        Vec_IntClear( p->vActive );
        Vec_IntClear( vLits );
        Vec_IntClear( vTargets );
        Vec_IntClear( vStore );
        Vec_IntClear( vFail );
        Vec_IntForEachEntry( vWork, Key, i )
        {
            p->pActive[Key] = 0;
            Lit = Cec3_Root( p, Key, &Target );
            Vec_IntPush( vLits, Lit );
            Vec_IntPush( vTargets, Target );
        }
        if ( !p->nCoreInitial )
            p->nCoreInitial = Gia_ManObjNum( p->pCore );
        Vec_StrFillExtra( p->vProven, 2 * Gia_ManObjNum( p->pCore ), 0 );
        Vec_IntFillExtra( p->vSeen, 2 * Gia_ManObjNum( p->pCore ), 0 );
        if ( !p->pSat )
        {
            p->pSat = Cbs_ManAlloc( p->pCore );
            Cbs_ManSetConflictNum( p->pSat, p->pPars->nBTLimit );
        }
        Cbs_ManSyncCore( p->pSat );
        Cec3_CoreSimulate( p );
        p->tSrm += Abc_Clock() - clk;
        clk = Abc_Clock();
        p->SolveStamp++;
        Vec_IntClear( vDefer );
        for ( Pass = 0; Pass < 2; Pass++ )
        {
            if ( Pass && ( Vec_IntSize( vStore ) || Vec_IntSize( vFail ) ) )
            {
                // Deferred roots stay active.  Mark only the replay-fallback
                // list: -1 means unattempted, not proved or failed.
                nDeferred += Vec_IntSize( vDefer );
                Vec_IntForEachEntry( vDefer, i, n )
                    Vec_IntWriteEntry( vLits, i, -1 );
                break;
            }
            nItems = Pass ? Vec_IntSize( vDefer ) : Vec_IntSize( vLits );
            for ( n = 0; n < nItems; n++ )
            {
                i = Pass ? Vec_IntEntry( vDefer, n ) : n;
                Lit = Vec_IntEntry( vLits, i );
                if ( !Lit || Vec_StrEntry( p->vProven, Lit ) )
                {
                    p->nReuse++;
                    continue;
                }
                Key = Vec_IntEntry( vWork, i );
                Target = Vec_IntEntry( vTargets, i );
                if ( Lit == 1 )
                {
                    Vec_IntPush( vFail, Target );
                    continue;
                }
                Cec3_Activate( p, Key % p->nObjs, Key / p->nObjs );
                if ( Vec_IntEntry( p->vSeen, Lit ) == p->SolveStamp )
                {
                    p->nReuse++;
                    continue;
                }
                // A previous expensive UNSAT proof is only a scheduling hint,
                // never evidence about a changed cone.  Try other obligations
                // first for up to CEC3_DEFER_LIMIT first-pass skips since that
                // proof.  Counterexamples and timeouts keep the count; only a
                // new UNSAT proof resets it (hard) or clears it (cheap).
                if ( !Pass && p->pHard[Key] && p->pHard[Key] <= CEC3_DEFER_LIMIT )
                {
                    p->pHard[Key]++;
                    Vec_IntPush( vDefer, i );
                    continue;
                }
                Vec_IntWriteEntry( p->vSeen, Lit, p->SolveStamp );
                if ( Cec3_CoreWitness( p, Lit ) )
                {
                    Vec_IntPush( vStore, Vec_IntSize( p->vModel ) );
                    Vec_IntAppend( vStore, p->vModel );
                    continue;
                }
                p->nSat++;
                Status = Cbs_ManSolve( p->pSat, Gia_ObjFromLit( p->pCore, Lit ) );
                if ( Status == 1 )
                {
                    Vec_StrWriteEntry( p->vProven, Lit, 1 );
                    p->pHard[Key] = Cbs_ManReadConflictNum( p->pSat ) >= CEC3_HARD_CONFLICTS;
                }
                else if ( Status == -1 )
                {
                    p->nUnknown++;
                    Vec_IntPush( vFail, Target );
                }
                else
                {
                    Vec_Int_t * vModel = Cbs_ReadModel( p->pSat );
                    Vec_IntPush( vStore, Vec_IntSize( vModel ) );
                    Vec_IntAppend( vStore, vModel );
                }
            }
        }
        p->tSat += Abc_Clock() - clk;
        clk = Abc_Clock();
        if ( Vec_IntSize( vStore ) )
            Cec3_Resimulate( p, vStore );
        Vec_IntForEachEntry( vFail, Target, i )
            Cec3_Remove( p, Target );
        // A SAT cube may expose an upstream speculative assumption instead
        // of its endpoint.  If replay changed nothing, drop an unresolved
        // endpoint conservatively; never interpret a failed replay as UNSAT.
        if ( Vec_IntSize( vStore ) && p->nSplits == nSplitsBefore )
        {
            p->nReplayFallback++;
            Vec_IntForEachEntry( vLits, Lit, i )
                if ( Lit > 0 && !Vec_StrEntry( p->vProven, Lit ) )
                    Cec3_Remove( p, Vec_IntEntry( vTargets, i ) );
        }
        p->tSim += Abc_Clock() - clk;
    }
    if ( p->nRounds == 100000 )
        fOk = 0;
    if ( p->pPars->fVerbose )
    {
        Abc_Print( 1, "scorr3 replay: deferred=%lld batches=%d dense=%d unknown=%d fallback=%d witnessed=%lld\n",
                   (long long)nDeferred, p->nBatches,
                   p->nDense, p->nUnknown, p->nReplayFallback, (long long)p->nSimSat );
        Abc_Print( 1,
                   "scorr3 %s: rounds=%d rebuilds=%d sat=%lld reuse=%lld invalidated=%lld sim-updates=%lld  "
                   "srm=%.3f sat=%.3f sim=%.3f sec\n",
                   p->fBase ? "base" : "step", p->nRounds, p->nRebuilds - 1, (long long)p->nSat, (long long)p->nReuse,
                   (long long)p->nUpdates, (long long)p->nSimUpdates, Cec3_Seconds( p->tSrm ),
                   Cec3_Seconds( p->tSat ), Cec3_Seconds( p->tSim ) );
    }
    Vec_IntFree( vWork );
    Vec_IntFree( vLits );
    Vec_IntFree( vTargets );
    Vec_IntFree( vStore );
    Vec_IntFree( vFail );
    Vec_IntFree( vDefer );
    return fOk;
}

// The checker deliberately reconstructs obligations through the established
// nonincremental builders, independently of the new cache and work queues.
/**Function*************************************************************

  Synopsis    [Independently audits the final base and step obligations.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec3_Check( Gia_Man_t * pAig, Cec_ParCor_t * pPars )
{
    extern Gia_Man_t * Gia_ManCorrSpecReduceInit( Gia_Man_t *, int, int, int, Vec_Int_t **, int );
    int Phase, Status, Out;
    for ( Phase = 0; Phase < 2; Phase++ )
    {
        Vec_Int_t * vPairs = NULL, * vCex = NULL;
        Vec_Str_t * vStatus = NULL;
        Gia_Man_t * pSrm = Phase ? Gia_ManCorrSpecReduce( pAig, pPars->nFrames, 1, &vPairs, 1, NULL )
                                 : Gia_ManCorrSpecReduceInit( pAig, pPars->nFrames, 0, 1, &vPairs, 1 );
        Status = Cec_ManCorrKissatCertify( pSrm, vPairs, &vCex, &vStatus, &Out, 0 );
        Abc_Print( 1, "scorr3 audit %s: %s\n", Phase ? "step" : "base",
                   Status == 1   ? "PASS"
                   : Status == 0 ? "FAIL"
                                 : "UNKNOWN" );
        Gia_ManStop( pSrm );
        Vec_IntFree( vPairs );
        Vec_IntFree( vCex );
        Vec_StrFree( vStatus );
        if ( Status != 1 )
            return 0;
    }
    return 1;
}

// Initial simulation uses fixed slices instead of allocating and releasing
// a simulation record at every gate in every round.  The established class
// comparison and splitting routines read these slices through pSimInfo.
/**Function*************************************************************

  Synopsis    [Performs one initial simulation and refinement round.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static void Cec3_InitialRound( Cec_ManSim_t * p )
{
    extern int Cec_ManSimCompareConst( unsigned *, int );
    extern int Cec_ManSimClassRefineOne( Cec_ManSim_t *, int );
    Gia_Obj_t * pObj;
    int i, w, k, Size, * pTable;
    unsigned * pValues = p->pMems + 1;
    Vec_IntClear( p->vRefinedC );
    Gia_ManForEachObj1( p->pAig, pObj, i )
    {
        unsigned * pRes = pValues + p->pSimInfo[i];
        if ( Gia_ObjIsCi( pObj ) )
        {
            assert( pRes == Vec_PtrEntry( p->vCiSimInfo, Gia_ObjCioId( pObj ) ) );
            pRes[0] &= ~1u;
        }
        else if ( Gia_ObjIsCo( pObj ) )
        {
            unsigned * pInput = pValues + p->pSimInfo[Gia_ObjFaninId0( pObj, i )];
            unsigned Mask = -(unsigned)Gia_ObjFaninC0( pObj );
            if ( p->vCoSimInfo && Gia_ObjIsRi( p->pAig, pObj ) )
            {
                unsigned * pOutput = (unsigned *)Vec_PtrEntry( p->vCoSimInfo, Gia_ObjCioId( pObj ) );
                for ( w = 0; w < p->nWords; w++ )
                    pOutput[w] = pInput[w] ^ Mask;
            }
            continue;
        }
        else
        {
            unsigned * a = pValues + p->pSimInfo[Gia_ObjFaninId0( pObj, i )];
            unsigned * b = pValues + p->pSimInfo[Gia_ObjFaninId1( pObj, i )];
            unsigned Mask0 = -(unsigned)Gia_ObjFaninC0( pObj );
            unsigned Mask1 = -(unsigned)Gia_ObjFaninC1( pObj );
            for ( w = 0; w < p->nWords; w++ )
                pRes[w] = ( a[w] ^ Mask0 ) & ( b[w] ^ Mask1 );
        }
        if ( Gia_ObjIsConst( p->pAig, i ) && !Cec_ManSimCompareConst( pRes, p->nWords ) )
            Vec_IntPush( p->vRefinedC, i );
        if ( Gia_ObjIsTail( p->pAig, i ) )
            Cec_ManSimClassRefineOne( p, Gia_ObjRepr( p->pAig, i ) );
    }
    if ( !Vec_IntSize( p->vRefinedC ) )
        return;
    // Match the existing candidate-constant partition, including its order,
    // without the recyclable-memory bookkeeping attached to each member.
    Size = Abc_PrimeCudd( 100 + Vec_IntSize( p->vRefinedC ) / 3 );
    pTable = ABC_CALLOC( int, Size );
    Vec_IntForEachEntry( p->vRefinedC, i, k )
    {
        int Key = Cec_ManSimHashKey( pValues + p->pSimInfo[i], p->nWords, Size );
        if ( !pTable[Key] )
            Gia_ObjSetRepr( p->pAig, i, GIA_VOID );
        else
        {
            int Repr = Gia_ObjRepr( p->pAig, pTable[Key] );
            Gia_ObjSetNext( p->pAig, pTable[Key], i );
            Gia_ObjSetRepr( p->pAig, i, Repr == GIA_VOID ? pTable[Key] : Repr );
        }
        pTable[Key] = i;
    }
    Vec_IntForEachEntry( p->vRefinedC, i, k )
        if ( Gia_ObjIsHead( p->pAig, i ) )
            Cec_ManSimClassRefineOne( p, i );
    ABC_FREE( pTable );
}
/**Function*************************************************************

  Synopsis    [Creates initial candidate classes using flat simulation storage.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Cec3_InitialClasses( Cec_ManSim_t * p )
{
    extern void Cec_ManSimCreateInfo( Cec_ManSim_t *, Vec_Ptr_t *, Vec_Ptr_t * );
    Gia_Obj_t * pObj;
    int i, Round, nWords = p->pPars->nWords;
    ABC_INT64_T nSize = (ABC_INT64_T)nWords * Gia_ManObjNum( p->pAig ) + 1;
    if ( p->pAig->nSimWords || nWords < 1 || nSize > INT_MAX )
        return 0;
    assert( p->pMems == NULL );
    p->pMems = ABC_CALLOC( unsigned, (size_t)nSize );
    p->pAig->pReprs = ABC_CALLOC( Gia_Rpr_t, Gia_ManObjNum( p->pAig ) );
    p->pAig->pNexts = ABC_CALLOC( int, Gia_ManObjNum( p->pAig ) );
    Gia_ManCreateValueRefs( p->pAig );
    Gia_ManForEachObj( p->pAig, pObj, i )
    {
        p->pSimInfo[i] = i * nWords;
        Gia_ObjSetRepr( p->pAig, i, Gia_ObjIsAnd( pObj ) ? 0 : GIA_VOID );
    }
    // These vectors own only pointer arrays; pMems owns the values.
    // Input generation and register carry address the flat slices directly.
    // Primary outputs are not read during candidate generation.
    Vec_PtrFree( p->vCiSimInfo );
    p->vCiSimInfo = Vec_PtrAlloc( Gia_ManCiNum(p->pAig) );
    Gia_ManForEachCi( p->pAig, pObj, i )
        Vec_PtrPush( p->vCiSimInfo, p->pMems + 1 + p->pSimInfo[Gia_ObjId(p->pAig, pObj)] );
    if ( p->vCoSimInfo )
    {
        Vec_PtrFree( p->vCoSimInfo );
        p->vCoSimInfo = Vec_PtrAlloc( Gia_ManCoNum(p->pAig) );
        Gia_ManForEachCo( p->pAig, pObj, i )
            Vec_PtrPush( p->vCoSimInfo, Gia_ObjIsRi(p->pAig, pObj) ?
                p->pMems + 1 + p->pSimInfo[Gia_ObjId(p->pAig, pObj)] : NULL );
    }
    Gia_ManForEachRo( p->pAig, pObj, i )
        if ( pObj->Value )
            Gia_ObjSetRepr( p->pAig, Gia_ObjId( p->pAig, pObj ), 0 );
    p->nWords = 1;
    for ( ;; )
    {
        for ( Round = 0; Round < 4; Round++ )
        {
            Cec_ManSimCreateInfo( p, p->vCiSimInfo, p->vCoSimInfo );
            Cec3_InitialRound( p );
        }
        if ( p->nWords > ( nWords - 1 ) / 2 )
            break;
        p->nWords = 2 * p->nWords + 1;
    }
    p->nWords = nWords;
    for ( Round = 0; Round < p->pPars->nRounds; Round++ )
    {
        Cec_ManSimCreateInfo( p, p->vCiSimInfo, p->vCoSimInfo );
        Cec3_InitialRound( p );
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Computes signal correspondence with persistent speculative reduction.]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Cec_ManLSCorrespondence3( Gia_Man_t * pAig, Cec_ParCor_t * pPars )
{
    extern Gia_Man_t * Gia_ManCorrReduce( Gia_Man_t * );
    Cec_ParSim_t SimPars;
    Cec_ManSim_t * pSim;
    Cec3_Man_t * p;
    Gia_Man_t * pNew, * pTemp;
    int fOwnFanout = pAig->vFanout == NULL, fOk, i;
    Gia_Obj_t * pObj;
    abctime clk = Abc_Clock();
    // Representatives have the lowest object ID in their class.  Putting
    // CIs first ensures a register can only map to a register or constant
    // during counterexample replay.  Reject before modifying the input.
    if ( !Gia_ManIsNormalized( pAig ) )
    {
        Abc_Print( -1, "scorr3: normalize the AIG (CIs first, COs last) before correspondence.\n" );
        return NULL;
    }
    if ( Gia_ManXorNum(pAig) || Gia_ManMuxNum(pAig) || Gia_ManBufNum(pAig) )
    {
        Abc_Print( -1, "scorr3: expand XORs, MUXes, and buffers into an AND/inverter graph first.\n" );
        return NULL;
    }
    if ( pPars->nFrames < 1 || 3 * ( (ABC_INT64_T)pPars->nFrames + 2 ) * Gia_ManObjNum( pAig ) > INT_MAX - 64 )
    {
        Abc_Print( -1, "scorr3: timeframe/object count exceeds indexing capacity.\n" );
        return NULL;
    }
    ABC_FREE( pAig->pReprs );
    ABC_FREE( pAig->pNexts );
    Gia_ManRandom( 1 );
    Cec_ManSimSetDefaultParams( &SimPars );
    SimPars.nWords = pPars->nWords;
    SimPars.nFrames = pPars->nFrames;
    SimPars.fSeqSimulate = 1;
    pSim = Cec_ManSimStart( pAig, &SimPars );
    if ( !Cec3_InitialClasses( pSim ) )
    {
        Cec_ManSimClassesPrepare( pSim, -1 );
        Cec_ManSimClassesRefine( pSim );
    }
    Cec_ManSimStop( pSim );
    if ( fOwnFanout )
        Gia_ManStaticFanoutStart( pAig );
    p = Cec3_Start( pAig, pPars, 1 );
    fOk = Cec3_Run( p );
    Cec3_Stop( p );
    if ( fOk )
    {
        p = Cec3_Start( pAig, pPars, 0 );
        fOk = Cec3_Run( p );
        Cec3_Stop( p );
    }
    if ( fOwnFanout )
        Gia_ManStaticFanoutStop( pAig );
    if ( fOk && pPars->fKissatCert )
        fOk = Cec3_Check( pAig, pPars );
    if ( !fOk )
    {
        ABC_FREE( pAig->pReprs );
        ABC_FREE( pAig->pNexts );
        Abc_Print( -1, "scorr3: no reduction returned.\n" );
        return NULL;
    }
    pTemp = Gia_ManCorrReduce( pAig );
    pTemp->nConstrs = pAig->nConstrs;
    pNew = Gia_ManSeqCleanup( pTemp );
    // Reduction preserves CI/CO order; cleanup leaves the surviving-object
    // map in Value.  Use that map for register names as well as PI/PO names.
    if ( pAig->vNamesIn )
    {
        pNew->vNamesIn = Vec_PtrAlloc( Gia_ManCiNum( pNew ) );
        Gia_ManForEachCi( pTemp, pObj, i )
            if ( ~pObj->Value )
                Vec_PtrPush( pNew->vNamesIn, i < Vec_PtrSize( pAig->vNamesIn )
                                                 ? Abc_UtilStrsav( (char *)Vec_PtrEntry( pAig->vNamesIn, i ) )
                                                 : NULL );
    }
    if ( pAig->vNamesOut )
    {
        pNew->vNamesOut = Vec_PtrAlloc( Gia_ManCoNum( pNew ) );
        Gia_ManForEachCo( pTemp, pObj, i )
            if ( ~pObj->Value )
                Vec_PtrPush( pNew->vNamesOut, i < Vec_PtrSize( pAig->vNamesOut )
                                                  ? Abc_UtilStrsav( (char *)Vec_PtrEntry( pAig->vNamesOut, i ) )
                                                  : NULL );
    }
    Gia_ManStop( pTemp );
    if ( pPars->fVerbose )
        Abc_Print( 1, "scorr3: ANDs %d -> %d  registers %d -> %d  total=%.3f sec\n", Gia_ManAndNum( pAig ),
                   Gia_ManAndNum( pNew ), Gia_ManRegNum( pAig ), Gia_ManRegNum( pNew ),
                   Cec3_Seconds( Abc_Clock() - clk ) );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                           END OF FILE                            ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
