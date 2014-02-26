/**CFile****************************************************************

  FileName    [ifDsd.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapping based on priority cuts.]

  Synopsis    [Computation of DSD representation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 21, 2006.]

  Revision    [$Id: ifTruth.c,v 1.00 2006/11/21 00:00:00 alanmi Exp $]

***********************************************************************/

#include "if.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// network types
typedef enum { 
    IF_DSD_NONE = 0,               // 0:  unknown
    IF_DSD_CONST0,                 // 1:  constant
    IF_DSD_VAR,                    // 2:  variable
    IF_DSD_AND,                    // 3:  AND
    IF_DSD_XOR,                    // 4:  XOR
    IF_DSD_MUX,                    // 5:  MUX
    IF_DSD_PRIME                   // 6:  PRIME
} If_DsdType_t;

typedef struct If_DsdObj_t_ If_DsdObj_t;
struct If_DsdObj_t_
{
    unsigned       Id;             // node ID
    unsigned       Type    :  3;   // node type
    unsigned       nSupp   :  5;   // variable
    unsigned       fMark   :  1;   // user mark
    unsigned       Count   : 18;   // variable
    unsigned       nFans   :  5;   // fanin count
    unsigned       pFans[0];       // fanins
};

struct If_DsdMan_t_
{
    int            nVars;          // max var number
    int            nWords;         // word number
    int            nBins;          // table size
    unsigned *     pBins;          // hash table
    Mem_Flex_t *   pMem;           // memory for nodes
    Vec_Ptr_t *    vObjs;          // objects
    Vec_Int_t *    vNexts;         // next pointers
    Vec_Int_t *    vNodes;         // temp
    word **        pTtElems;       // elementary TTs
    Vec_Mem_t *    vTtMem;         // truth table memory and hash table
    Vec_Ptr_t *    vTtDecs;        // truth table decompositions
    int            nUniqueHits;    // statistics
    int            nUniqueMisses;  // statistics
    abctime        timeBeg;        // statistics
    abctime        timeDec;        // statistics
    abctime        timeLook;       // statistics
    abctime        timeEnd;        // statistics
};

static inline int           If_DsdObjWordNum( int nFans )                                    { return sizeof(If_DsdObj_t) / 8 + nFans / 2 + ((nFans & 1) > 0);              }
static inline int           If_DsdObjTruthId( If_DsdMan_t * p, If_DsdObj_t * pObj )          { return pObj->Type == IF_DSD_PRIME ? pObj->pFans[pObj->nFans] : -1;           }
static inline word *        If_DsdObjTruth( If_DsdMan_t * p, If_DsdObj_t * pObj )            { return Vec_MemReadEntry(p->vTtMem, If_DsdObjTruthId(p, pObj));               }
static inline void          If_DsdObjSetTruth( If_DsdMan_t * p, If_DsdObj_t * pObj, int Id ) { assert( pObj->Type == IF_DSD_PRIME && pObj->nFans > 2 ); pObj->pFans[pObj->nFans] = Id;                    }

static inline void          If_DsdObjClean( If_DsdObj_t * pObj )                       { memset( pObj, 0, sizeof(If_DsdObj_t) );                                            }
static inline int           If_DsdObjId( If_DsdObj_t * pObj )                          { return pObj->Id;                                                                   }
static inline int           If_DsdObjType( If_DsdObj_t * pObj )                        { return pObj->Type;                                                                 }
static inline int           If_DsdObjIsVar( If_DsdObj_t * pObj )                       { return (int)(pObj->Type == IF_DSD_VAR);                                            }
static inline int           If_DsdObjSuppSize( If_DsdObj_t * pObj )                    { return pObj->nSupp;                                                                }
static inline int           If_DsdObjFaninNum( If_DsdObj_t * pObj )                    { return pObj->nFans;                                                                }
static inline int           If_DsdObjFaninC( If_DsdObj_t * pObj, int i )               { assert(i < (int)pObj->nFans); return Abc_LitIsCompl(pObj->pFans[i]);               }
static inline int           If_DsdObjFaninLit( If_DsdObj_t * pObj, int i )             { assert(i < (int)pObj->nFans); return pObj->pFans[i];                               }

static inline If_DsdObj_t * If_DsdVecObj( Vec_Ptr_t * p, int Id )                      { return (If_DsdObj_t *)Vec_PtrEntry(p, Id);                                         }
static inline If_DsdObj_t * If_DsdVecConst0( Vec_Ptr_t * p )                           { return If_DsdVecObj( p, 0 );                                                       }
static inline If_DsdObj_t * If_DsdVecVar( Vec_Ptr_t * p, int v )                       { return If_DsdVecObj( p, v+1 );                                                     }
static inline int           If_DsdVecObjSuppSize( Vec_Ptr_t * p, int iObj )            { return If_DsdVecObj( p, iObj )->nSupp;                                             }
static inline int           If_DsdVecLitSuppSize( Vec_Ptr_t * p, int iLit )            { return If_DsdVecObjSuppSize( p, Abc_Lit2Var(iLit) );                               }
static inline int           If_DsdVecObjRef( Vec_Ptr_t * p, int iObj )                 { return If_DsdVecObj( p, iObj )->Count;                                             }
static inline void          If_DsdVecObjIncRef( Vec_Ptr_t * p, int iObj )              { if ( If_DsdVecObjRef(p, iObj) < 0x3FFFF ) If_DsdVecObj( p, iObj )->Count++;        }
static inline If_DsdObj_t * If_DsdObjFanin( Vec_Ptr_t * p, If_DsdObj_t * pObj, int i ) { assert(i < (int)pObj->nFans); return If_DsdVecObj(p, Abc_Lit2Var(pObj->pFans[i])); }
static inline int           If_DsdVecObjMark( Vec_Ptr_t * p, int iObj )                { return If_DsdVecObj( p, iObj )->fMark;                                             }
static inline void          If_DsdVecObjSetMark( Vec_Ptr_t * p, int iObj )             { If_DsdVecObj( p, iObj )->fMark = 1;                                                }

#define If_DsdVecForEachObj( vVec, pObj, i )                \
    Vec_PtrForEachEntry( If_DsdObj_t *, vVec, pObj, i )
#define If_DsdVecForEachObjVec( vNodes, vVec, pObj, i )      \
    for ( i = 0; (i < Vec_IntSize(vNodes)) && ((pObj) = If_DsdVecObj(vVec, Vec_IntEntry(vNodes,i))); i++ )
#define If_DsdVecForEachNode( vVec, pObj, i )               \
    Vec_PtrForEachEntry( If_DsdObj_t *, vVec, pObj, i )     \
        if ( If_DsdObjType(pObj) == IF_DSD_CONST0 || If_DsdObjType(pObj) == IF_DSD_VAR ) {} else
#define If_DsdObjForEachFanin( vVec, pObj, pFanin, i )      \
    for ( i = 0; (i < If_DsdObjFaninNum(pObj)) && ((pFanin) = If_DsdObjFanin(vVec, pObj, i)); i++ )
#define If_DsdObjForEachFaninLit( vVec, pObj, iLit, i )      \
    for ( i = 0; (i < If_DsdObjFaninNum(pObj)) && ((iLit) = If_DsdObjFaninLit(pObj, i)); i++ )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
 
/**Function*************************************************************

  Synopsis    [Sorting DSD literals.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_DsdObjCompare( Vec_Ptr_t * p, int iLit0, int iLit1 )
{
    If_DsdObj_t * p0 = If_DsdVecObj(p, Abc_Lit2Var(iLit0));
    If_DsdObj_t * p1 = If_DsdVecObj(p, Abc_Lit2Var(iLit1));
    int i, Res;
    if ( If_DsdObjType(p0) < If_DsdObjType(p1) )
        return -1;
    if ( If_DsdObjType(p0) > If_DsdObjType(p1) )
        return 1;
    if ( If_DsdObjType(p0) < IF_DSD_AND )
        return 0;
    if ( If_DsdObjFaninNum(p0) < If_DsdObjFaninNum(p1) )
        return -1;
    if ( If_DsdObjFaninNum(p0) > If_DsdObjFaninNum(p1) )
        return 1;
    for ( i = 0; i < If_DsdObjFaninNum(p0); i++ )
    {
        Res = If_DsdObjCompare( p, If_DsdObjFaninLit(p0, i), If_DsdObjFaninLit(p1, i) );
        if ( Res != 0 )
            return Res;
    }
    if ( Abc_LitIsCompl(iLit0) < Abc_LitIsCompl(iLit1) )
        return -1;
    if ( Abc_LitIsCompl(iLit0) > Abc_LitIsCompl(iLit1) )
        return 1;
    return 0;
}
void If_DsdObjSort( Vec_Ptr_t * p, int * pLits, int nLits, int * pPerm )
{
    int i, j, best_i;
    for ( i = 0; i < nLits-1; i++ )
    {
        best_i = i;
        for ( j = i+1; j < nLits; j++ )
            if ( If_DsdObjCompare(p, pLits[best_i], pLits[j]) == 1 )
                best_i = j;
        if ( i == best_i )
            continue;
        ABC_SWAP( int, pLits[i], pLits[best_i] );
        if ( pPerm )
            ABC_SWAP( int, pPerm[i], pPerm[best_i] );
    }
}

/**Function*************************************************************

  Synopsis    [Creating DSD objects.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
If_DsdObj_t * If_DsdObjAlloc( If_DsdMan_t * p, int Type, int nFans )
{
    int nWords = If_DsdObjWordNum( nFans + (int)(Type == DAU_DSD_PRIME) );
    If_DsdObj_t * pObj = (If_DsdObj_t *)Mem_FlexEntryFetch( p->pMem, sizeof(word) * nWords );
    If_DsdObjClean( pObj );
    pObj->Type   = Type;
    pObj->nFans  = nFans;
    pObj->Id     = Vec_PtrSize( p->vObjs );
    pObj->fMark  = 0;
    pObj->Count  = 0;
    Vec_PtrPush( p->vObjs, pObj );
    Vec_IntPush( p->vNexts, 0 );
    return pObj;
}
int If_DsdObjCreate( If_DsdMan_t * p, int Type, int * pLits, int nLits, int truthId )
{
    If_DsdObj_t * pObj, * pFanin;
    int i, iPrev = -1;
    // check structural canonicity
    assert( Type != DAU_DSD_MUX || nLits == 3 );
    assert( Type != DAU_DSD_MUX || !Abc_LitIsCompl(pLits[0]) );
    assert( Type != DAU_DSD_MUX || !Abc_LitIsCompl(pLits[1]) || !Abc_LitIsCompl(pLits[2]) );
    // check that leaves are in good order
    if ( Type == DAU_DSD_AND || Type == DAU_DSD_XOR )
    {
        for ( i = 0; i < nLits; i++ )
        {
            pFanin = If_DsdVecObj( p->vObjs, Abc_Lit2Var(pLits[i]) );
            assert( Type != DAU_DSD_AND || Abc_LitIsCompl(pLits[i]) || If_DsdObjType(pFanin) != DAU_DSD_AND );
            assert( Type != DAU_DSD_XOR || If_DsdObjType(pFanin) != DAU_DSD_XOR );
            assert( iPrev == -1 || If_DsdObjCompare(p->vObjs, iPrev, pLits[i]) <= 0 );
            iPrev = pLits[i];
        }
    }
    // create new node
    pObj = If_DsdObjAlloc( p, Type, nLits );
    if ( Type == DAU_DSD_PRIME )
        If_DsdObjSetTruth( p, pObj, truthId );
    assert( pObj->nSupp == 0 );
    for ( i = 0; i < nLits; i++ )
    {
        pObj->pFans[i] = pLits[i];
        pObj->nSupp += If_DsdVecLitSuppSize(p->vObjs, pLits[i]);
    }
/*
    {
        extern void If_DsdManPrintOne( If_DsdMan_t * p, int iDsdLit, int * pPermLits );
        If_DsdManPrintOne( p, If_DsdObj2Lit(pObj), NULL );
    }
*/
    return pObj->Id;
}

/**Function*************************************************************

  Synopsis    [DSD manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word ** If_ManDsdTtElems()
{
    static word TtElems[DAU_MAX_VAR+1][DAU_MAX_WORD], * pTtElems[DAU_MAX_VAR+1] = {NULL};
    if ( pTtElems[0] == NULL )
    {
        int v;
        for ( v = 0; v <= DAU_MAX_VAR; v++ )
            pTtElems[v] = TtElems[v];
        Abc_TtElemInit( pTtElems, DAU_MAX_VAR );
    }
    return pTtElems;
}
If_DsdMan_t * If_DsdManAlloc( int nVars )
{
    If_DsdMan_t * p;
    p = ABC_CALLOC( If_DsdMan_t, 1 );
    p->nVars  = nVars;
    p->nWords = Abc_TtWordNum( nVars );
    p->nBins  = Abc_PrimeCudd( 1000000 );
    p->pBins  = ABC_CALLOC( unsigned, p->nBins );
    p->pMem   = Mem_FlexStart();
    p->vObjs  = Vec_PtrAlloc( 10000 );
    p->vNexts = Vec_IntAlloc( 10000 );
    If_DsdObjAlloc( p, IF_DSD_CONST0, 0 );
    If_DsdObjAlloc( p, IF_DSD_VAR, 0 )->nSupp = 1;
    p->vNodes   = Vec_IntAlloc( 32 );
    p->pTtElems = If_ManDsdTtElems();
    p->vTtDecs  = Vec_PtrAlloc( 1000 );
    p->vTtMem   = Vec_MemAlloc( Abc_TtWordNum(nVars), 12 );
    Vec_MemHashAlloc( p->vTtMem, 10000 );
    return p;
}
void If_DsdManFree( If_DsdMan_t * p )
{
    int fVerbose = 0;
//    If_DsdManDump( p );
    If_DsdManPrint( p, NULL, 0 );
    Vec_MemDumpTruthTables( p->vTtMem, "dumpdsd", p->nVars );
    if ( fVerbose )
    {
        Abc_PrintTime( 1, "Time begin ", p->timeBeg );
        Abc_PrintTime( 1, "Time decomp", p->timeDec );
        Abc_PrintTime( 1, "Time lookup", p->timeLook );
        Abc_PrintTime( 1, "Time end   ", p->timeEnd );
    }
    Vec_VecFree( (Vec_Vec_t *)p->vTtDecs );
    Vec_MemHashFree( p->vTtMem );
    Vec_MemFreeP( &p->vTtMem );
    Vec_IntFreeP( &p->vNodes );
    Vec_IntFreeP( &p->vNexts );
    Vec_PtrFreeP( &p->vObjs );
    Mem_FlexStop( p->pMem, 0 );
    ABC_FREE( p->pBins );
    ABC_FREE( p );
}
int If_DsdManCheckNonDec_rec( If_DsdMan_t * p, int Id )
{
    If_DsdObj_t * pObj;
    int i, iFanin;
    pObj = If_DsdVecObj( p->vObjs, Id );
    if ( If_DsdObjType(pObj) == IF_DSD_CONST0 )
        return 0;
    if ( If_DsdObjType(pObj) == IF_DSD_VAR )
        return 0;
    if ( If_DsdObjType(pObj) == IF_DSD_PRIME )
        return 1;
    If_DsdObjForEachFaninLit( p->vObjs, pObj, iFanin, i )
        if ( If_DsdManCheckNonDec_rec( p, Abc_Lit2Var(iFanin) ) )
            return 1;
    return 0;
}
void If_DsdManPrint_rec( FILE * pFile, If_DsdMan_t * p, int iDsdLit, unsigned char * pPermLits, int * pnSupp )
{
    char OpenType[7]  = {0, 0, 0, '(', '[', '<', '{'};
    char CloseType[7] = {0, 0, 0, ')', ']', '>', '}'};
    If_DsdObj_t * pObj;
    int i, iFanin;
    fprintf( pFile, "%s", Abc_LitIsCompl(iDsdLit) ? "!" : ""  );
    pObj = If_DsdVecObj( p->vObjs, Abc_Lit2Var(iDsdLit) );
    if ( If_DsdObjType(pObj) == IF_DSD_CONST0 )
        { fprintf( pFile, "0" ); return; }
    if ( If_DsdObjType(pObj) == IF_DSD_VAR )
    {
        int iPermLit = pPermLits ? (int)pPermLits[(*pnSupp)++] : Abc_Var2Lit((*pnSupp)++, 0);
        fprintf( pFile, "%s%c", Abc_LitIsCompl(iPermLit)? "!":"", 'a' + Abc_Lit2Var(iPermLit) );
        return;
    }
    if ( If_DsdObjType(pObj) == IF_DSD_PRIME )
        Abc_TtPrintHexRev( pFile, If_DsdObjTruth(p, pObj), If_DsdObjFaninNum(pObj) );
    fprintf( pFile, "%c", OpenType[If_DsdObjType(pObj)] );
    If_DsdObjForEachFaninLit( p->vObjs, pObj, iFanin, i )
        If_DsdManPrint_rec( pFile, p, iFanin, pPermLits, pnSupp );
    fprintf( pFile, "%c", CloseType[If_DsdObjType(pObj)] );
}
void If_DsdManPrintOne( FILE * pFile, If_DsdMan_t * p, int iObjId, unsigned char * pPermLits, int fNewLine )
{
    int nSupp = 0;
    fprintf( pFile, "%6d : ", iObjId );
    fprintf( pFile, "%2d ",   If_DsdVecObjSuppSize(p->vObjs, iObjId) );
    fprintf( pFile, "%8d ",   If_DsdVecObjRef(p->vObjs, iObjId) );
    If_DsdManPrint_rec( pFile, p, Abc_Var2Lit(iObjId, 0), pPermLits, &nSupp );
    if ( fNewLine )
        fprintf( pFile, "\n" );
    assert( nSupp == If_DsdVecObjSuppSize(p->vObjs, iObjId) );
}
void If_DsdManPrint( If_DsdMan_t * p, char * pFileName, int fVerbose )
{
    If_DsdObj_t * pObj;
    int DsdMax = 0, CountUsed = 0, CountNonDsdStr = 0;
    int i, clk = Abc_Clock();
    FILE * pFile;
    pFile = pFileName ? fopen( pFileName, "wb" ) : stdout;
    if ( pFileName && pFile == NULL )
    {
        printf( "cannot open output file\n" );
        return;
    }
    If_DsdVecForEachObj( p->vObjs, pObj, i )
    {
        if ( If_DsdObjType(pObj) == IF_DSD_PRIME )
            DsdMax = Abc_MaxInt( DsdMax, pObj->nFans ); 
        CountNonDsdStr += If_DsdManCheckNonDec_rec( p, pObj->Id );
        CountUsed += ( If_DsdVecObjRef(p->vObjs, pObj->Id) > 0 );
    }
    fprintf( pFile, "Total number of objects    = %8d\n", Vec_PtrSize(p->vObjs) );
    fprintf( pFile, "Externally used objects    = %8d\n", CountUsed );
    fprintf( pFile, "Non-DSD objects (max =%2d)  = %8d\n", DsdMax, Vec_MemEntryNum(p->vTtMem) );
    fprintf( pFile, "Non-DSD structures         = %8d\n", CountNonDsdStr );
    fprintf( pFile, "Unique table hits          = %8d\n", p->nUniqueHits );
    fprintf( pFile, "Unique table misses        = %8d\n", p->nUniqueMisses );
    fprintf( pFile, "Memory used for objects    = %8.2f MB.\n", 1.0*Mem_FlexReadMemUsage(p->pMem)/(1<<20) );
    fprintf( pFile, "Memory used for hash table = %8.2f MB.\n", 1.0*sizeof(int)*p->nBins/(1<<20) );
    fprintf( pFile, "Memory used for array      = %8.2f MB.\n", 1.0*sizeof(void *)*Vec_PtrCap(p->vObjs)/(1<<20) );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
//    If_DsdManHashProfile( p );
//    If_DsdManDump( p );
//    return;
    if ( !fVerbose )
        return;
    If_DsdVecForEachObj( p->vObjs, pObj, i )
    {
//        if ( i == 50 )
//            break;
        If_DsdManPrintOne( pFile, p, pObj->Id, NULL, 1 );
    }
    fprintf( pFile, "\n" );
    if ( pFileName )
        fclose( pFile );
}
void If_DsdManDump( If_DsdMan_t * p )
{
    char * pFileName = "dss_tts.txt";
    FILE * pFile;
    If_DsdObj_t * pObj;
    int i;
    pFile = fopen( pFileName, "wb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\".\n", pFileName );
        return;
    }
    If_DsdVecForEachObj( p->vObjs, pObj, i )
    {
        if ( If_DsdObjType(pObj) != IF_DSD_PRIME )
            continue;
        fprintf( pFile, "0x" );
        Abc_TtPrintHexRev( pFile, If_DsdObjTruth(p, pObj), p->nVars );
        fprintf( pFile, "\n" );
        printf( "    " );
        Dau_DsdPrintFromTruth( If_DsdObjTruth(p, pObj), p->nVars );
    }
    fclose( pFile );
}

/**Function*************************************************************

  Synopsis    [Collect nodes of the tree.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_DsdManCollect_rec( If_DsdMan_t * p, int Id, Vec_Int_t * vNodes )
{
    int i, iFanin;
    If_DsdObj_t * pObj = If_DsdVecObj( p->vObjs, Id );
    if ( If_DsdObjType(pObj) == IF_DSD_CONST0 || If_DsdObjType(pObj) == IF_DSD_VAR )
        return;
    If_DsdObjForEachFaninLit( p->vObjs, pObj, iFanin, i )
        If_DsdManCollect_rec( p, Abc_Lit2Var(iFanin), vNodes );
    Vec_IntPush( vNodes, Id );
}
void If_DsdManCollect( If_DsdMan_t * p, int Id, Vec_Int_t * vNodes )
{
    Vec_IntClear( vNodes );
    If_DsdManCollect_rec( p, Id, vNodes );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_DsdManHashProfile( If_DsdMan_t * p )
{
    If_DsdObj_t * pObj;
    unsigned * pSpot;
    int i, Counter;
    for ( i = 0; i < p->nBins; i++ )
    {
        Counter = 0;
        for ( pSpot = p->pBins + i; *pSpot; pSpot = (unsigned *)Vec_IntEntryP(p->vNexts, pObj->Id), Counter++ )
             pObj = If_DsdVecObj( p->vObjs, *pSpot );
        if ( Counter )
            printf( "%d ", Counter );
    }
    printf( "\n" );
}
static inline unsigned If_DsdObjHashKey( If_DsdMan_t * p, int Type, int * pLits, int nLits, int truthId )
{
    static int s_Primes[8] = { 1699, 4177, 5147, 5647, 6343, 7103, 7873, 8147 };
    int i;
    unsigned uHash = Type * 7873 + nLits * 8147;
    for ( i = 0; i < nLits; i++ )
        uHash += pLits[i] * s_Primes[i & 0x7];
    if ( Type == IF_DSD_PRIME )
        uHash += truthId * s_Primes[i & 0x7];
    return uHash % p->nBins;
}
unsigned * If_DsdObjHashLookup( If_DsdMan_t * p, int Type, int * pLits, int nLits, int truthId )
{
    If_DsdObj_t * pObj;
    unsigned * pSpot = p->pBins + If_DsdObjHashKey(p, Type, pLits, nLits, truthId);
    for ( ; *pSpot; pSpot = (unsigned *)Vec_IntEntryP(p->vNexts, pObj->Id) )
    {
        pObj = If_DsdVecObj( p->vObjs, *pSpot );
        if ( If_DsdObjType(pObj) == Type && 
             If_DsdObjFaninNum(pObj) == nLits && 
             !memcmp(pObj->pFans, pLits, sizeof(int)*If_DsdObjFaninNum(pObj)) &&
             truthId == If_DsdObjTruthId(p, pObj) )
        {
            p->nUniqueHits++;
            return pSpot;
        }
    }
    p->nUniqueMisses++;
    return pSpot;
}
int If_DsdObjFindOrAdd( If_DsdMan_t * p, int Type, int * pLits, int nLits, word * pTruth )
{
    int truthId = (Type == IF_DSD_PRIME) ? Vec_MemHashInsert(p->vTtMem, pTruth) : -1;
    unsigned * pSpot = If_DsdObjHashLookup( p, Type, pLits, nLits, truthId );
    if ( *pSpot )
        return *pSpot;
    if ( truthId >= 0 && truthId == Vec_MemEntryNum(p->vTtMem)-1 )
    {
        Vec_Int_t * vSets = Dau_DecFindSets( pTruth, nLits );
        Vec_PtrPush( p->vTtDecs, vSets );
//        Dau_DecPrintSets( vSets, nLits );
    }
    *pSpot = Vec_PtrSize( p->vObjs );
    return If_DsdObjCreate( p, Type, pLits, nLits, truthId );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void If_DsdManComputeTruth_rec( If_DsdMan_t * p, int iDsd, word * pRes, unsigned char * pPermLits, int * pnSupp )
{
    int i, iFanin, fCompl = Abc_LitIsCompl(iDsd);
    If_DsdObj_t * pObj = If_DsdVecObj( p->vObjs, Abc_Lit2Var(iDsd) );
    if ( If_DsdObjType(pObj) == IF_DSD_VAR )
    {
        int iPermLit = (int)pPermLits[(*pnSupp)++];
        assert( (*pnSupp) <= p->nVars );
        Abc_TtCopy( pRes, p->pTtElems[Abc_Lit2Var(iPermLit)], p->nWords, fCompl ^ Abc_LitIsCompl(iPermLit) );
        return;
    }
    if ( If_DsdObjType(pObj) == IF_DSD_AND || If_DsdObjType(pObj) == IF_DSD_XOR )
    {
        word pTtTemp[DAU_MAX_WORD];
        if ( If_DsdObjType(pObj) == IF_DSD_AND )
            Abc_TtConst1( pRes, p->nWords );
        else
            Abc_TtConst0( pRes, p->nWords );
        If_DsdObjForEachFaninLit( p->vObjs, pObj, iFanin, i )
        {
            If_DsdManComputeTruth_rec( p, iFanin, pTtTemp, pPermLits, pnSupp );
            if ( If_DsdObjType(pObj) == IF_DSD_AND )
                Abc_TtAnd( pRes, pRes, pTtTemp, p->nWords, 0 );
            else
                Abc_TtXor( pRes, pRes, pTtTemp, p->nWords, 0 );
        }
        if ( fCompl ) Abc_TtNot( pRes, p->nWords );
        return;
    }
    if ( If_DsdObjType(pObj) == IF_DSD_MUX ) // mux
    {
        word pTtTemp[3][DAU_MAX_WORD];
        If_DsdObjForEachFaninLit( p->vObjs, pObj, iFanin, i )
            If_DsdManComputeTruth_rec( p, iFanin, pTtTemp[i], pPermLits, pnSupp );
        assert( i == 3 );
        Abc_TtMux( pRes, pTtTemp[0], pTtTemp[1], pTtTemp[2], p->nWords );
        if ( fCompl ) Abc_TtNot( pRes, p->nWords );
        return;
    }
    if ( If_DsdObjType(pObj) == IF_DSD_PRIME ) // function
    {
        word pFanins[DAU_MAX_VAR][DAU_MAX_WORD];
        If_DsdObjForEachFaninLit( p->vObjs, pObj, iFanin, i )
            If_DsdManComputeTruth_rec( p, iFanin, pFanins[i], pPermLits, pnSupp );
        Dau_DsdTruthCompose_rec( If_DsdObjTruth(p, pObj), pFanins, pRes, pObj->nFans, p->nWords );
        if ( fCompl ) Abc_TtNot( pRes, p->nWords );
        return;
    }
    assert( 0 );

}
word * If_DsdManComputeTruth( If_DsdMan_t * p, int iDsd, unsigned char * pPermLits )
{
    int nSupp = 0;
    word * pRes = p->pTtElems[DAU_MAX_VAR];
    If_DsdObj_t * pObj = If_DsdVecObj( p->vObjs, Abc_Lit2Var(iDsd) );
    if ( iDsd == 0 )
        Abc_TtConst0( pRes, p->nWords );
    else if ( iDsd == 1 )
        Abc_TtConst1( pRes, p->nWords );
    else if ( pObj->Type == IF_DSD_VAR )
    {
        int iPermLit = (int)pPermLits[nSupp++];
        Abc_TtCopy( pRes, p->pTtElems[Abc_Lit2Var(iPermLit)], p->nWords, Abc_LitIsCompl(iDsd) ^ Abc_LitIsCompl(iPermLit) );
    }
    else
        If_DsdManComputeTruth_rec( p, iDsd, pRes, pPermLits, &nSupp );
    assert( nSupp == If_DsdVecObjSuppSize(p->vObjs, Abc_Lit2Var(iDsd)) );
    return pRes;
}

/**Function*************************************************************

  Synopsis    [Performs DSD operation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_DsdManOperation2( If_DsdMan_t * p, int Type, int * pLits, int nLits )
{
    If_DsdObj_t * pObj;
    int nChildren = 0, pChildren[DAU_MAX_VAR];
    int i, k, Id, iFanin, fCompl = 0;
    if ( Type == IF_DSD_AND )
    {
        for ( k = 0; k < nLits; k++ )
        {
            pObj = If_DsdVecObj( p->vObjs, Abc_Lit2Var(pLits[k]) );
            if ( Abc_LitIsCompl(pLits[k]) || If_DsdObjType(pObj) != IF_DSD_AND )
                pChildren[nChildren++] = pLits[k];
            else
                If_DsdObjForEachFaninLit( p->vObjs, pObj, iFanin, i )
                    pChildren[nChildren++] = iFanin;
        }
        If_DsdObjSort( p->vObjs, pChildren, nChildren, NULL );
    }
    else if ( Type == IF_DSD_XOR )
    {
        for ( k = 0; k < nLits; k++ )
        {
            fCompl ^= Abc_LitIsCompl(pLits[k]);
            pObj = If_DsdVecObj( p->vObjs, Abc_LitRegular(pLits[k]) );
            if ( If_DsdObjType(pObj) != IF_DSD_XOR )
                pChildren[nChildren++] = pLits[k];
            else
                If_DsdObjForEachFaninLit( p->vObjs, pObj, iFanin, i )
                {
                    assert( !Abc_LitIsCompl(iFanin) );
                    pChildren[nChildren++] = iFanin;
                }
        }
        If_DsdObjSort( p->vObjs, pChildren, nChildren, NULL );
    }
    else if ( Type == IF_DSD_MUX )
    {
        if ( Abc_LitIsCompl(pLits[0]) )
        {
            pLits[0] = Abc_LitNot(pLits[0]);
            ABC_SWAP( int, pLits[1], pLits[2] );
        }
        if ( Abc_LitIsCompl(pLits[1]) )
        {
            pLits[1] = Abc_LitNot(pLits[1]);
            pLits[2] = Abc_LitNot(pLits[2]);
            fCompl ^= 1;
        }
        for ( k = 0; k < nLits; k++ )
            pChildren[nChildren++] = pLits[k];
    }
    else assert( 0 );
    // create new graph
    Id = If_DsdObjFindOrAdd( p, Type, pChildren, nChildren, NULL );
    return Abc_Var2Lit( Id, fCompl );
}

/**Function*************************************************************

  Synopsis    [Performs DSD operation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_DsdManOperation( If_DsdMan_t * p, int Type, int * pLits, int nLits, unsigned char * pPerm, word * pTruth )
{
    If_DsdObj_t * pObj, * pFanin;
    unsigned char pPermNew[DAU_MAX_VAR];
    int nChildren = 0, pChildren[DAU_MAX_VAR], pBegEnd[DAU_MAX_VAR];
    int i, k, j, Id, iFanin, fComplFan, fCompl = 0, nSSize = 0;
    if ( Type == IF_DSD_AND )
    {
        for ( k = 0; k < nLits; k++ )
        {
            pObj = If_DsdVecObj( p->vObjs, Abc_Lit2Var(pLits[k]) );
            if ( Abc_LitIsCompl(pLits[k]) || If_DsdObjType(pObj) != IF_DSD_AND )
            {
                fComplFan = If_DsdObjIsVar(pObj) && Abc_LitIsCompl(pLits[k]);
                pBegEnd[nChildren] = (nSSize << 16) | (fComplFan << 8) | (nSSize + pObj->nSupp);
                nSSize += pObj->nSupp;
                pChildren[nChildren++] = Abc_LitNotCond( pLits[k], fComplFan );
            }
            else
            {
                If_DsdObjForEachFaninLit( p->vObjs, pObj, iFanin, i )
                {
                    pFanin = If_DsdVecObj( p->vObjs, Abc_Lit2Var(iFanin) );
                    fComplFan = If_DsdObjIsVar(pFanin) && Abc_LitIsCompl(iFanin);
                    pBegEnd[nChildren] = (nSSize << 16) | (fComplFan << 8) | (nSSize + pFanin->nSupp);
                    pChildren[nChildren++] = Abc_LitNotCond( iFanin, fComplFan );
                    nSSize += pFanin->nSupp;
                }
            }
        }
        If_DsdObjSort( p->vObjs, pChildren, nChildren, pBegEnd );
        // create permutation
        for ( j = i = 0; i < nChildren; i++ )
            for ( k = (pBegEnd[i] >> 16); k < (pBegEnd[i] & 0xFF); k++ )
                pPermNew[j++] = (unsigned char)Abc_LitNotCond( pPerm[k], (pBegEnd[i] >> 8) & 1 );
        assert( j == nSSize );
        for ( j = 0; j < nSSize; j++ )
            pPerm[j] = pPermNew[j];
    }
    else if ( Type == IF_DSD_XOR )
    {
        fComplFan = 0;
        for ( k = 0; k < nLits; k++ )
        {
            fCompl ^= Abc_LitIsCompl(pLits[k]);
            pObj = If_DsdVecObj( p->vObjs, Abc_Lit2Var(pLits[k]) );
            if ( If_DsdObjType(pObj) != IF_DSD_XOR )
            {
                pBegEnd[nChildren] = (nSSize << 16) | (fComplFan << 8) | (nSSize + pObj->nSupp);
                pChildren[nChildren++] = Abc_LitRegular(pLits[k]);
                nSSize += pObj->nSupp;
            }
            else
            {
                If_DsdObjForEachFaninLit( p->vObjs, pObj, iFanin, i )
                {
                    assert( !Abc_LitIsCompl(iFanin) );
                    pFanin = If_DsdVecObj( p->vObjs, Abc_Lit2Var(iFanin) );
                    pBegEnd[nChildren] = (nSSize << 16) | (fComplFan << 8) | (nSSize + pFanin->nSupp);
                    pChildren[nChildren++] = Abc_LitRegular(iFanin);
                    nSSize += pFanin->nSupp;
                }
            }
        }
        If_DsdObjSort( p->vObjs, pChildren, nChildren, pBegEnd );
        // create permutation
        for ( j = i = 0; i < nChildren; i++ )
            for ( k = (pBegEnd[i] >> 16); k < (pBegEnd[i] & 0xFF); k++ )
                pPermNew[j++] = (unsigned char)Abc_LitNotCond( pPerm[k], (pBegEnd[i] >> 8) & 1 );
        assert( j == nSSize );
        for ( j = 0; j < nSSize; j++ )
            pPerm[j] = pPermNew[j];
    }
    else if ( Type == IF_DSD_MUX )
    {
        for ( k = 0; k < nLits; k++ )
        {
            pFanin = If_DsdVecObj( p->vObjs, Abc_Lit2Var(pLits[k]) );
            fComplFan = If_DsdObjIsVar(pFanin) && Abc_LitIsCompl(pLits[k]);
            pChildren[nChildren++] = Abc_LitNotCond( pLits[k], fComplFan );
            pPerm[k] = (unsigned char)Abc_LitNotCond( (int)pPerm[k], fComplFan );
            nSSize += pFanin->nSupp;
        }
        if ( Abc_LitIsCompl(pChildren[0]) )
        {
            If_DsdObj_t * pFans[3];
            pChildren[0] = Abc_LitNot(pChildren[0]);
            ABC_SWAP( int, pChildren[1], pChildren[2] );
            pFans[0] = If_DsdVecObj( p->vObjs, Abc_Lit2Var(pChildren[0]) );
            pFans[1] = If_DsdVecObj( p->vObjs, Abc_Lit2Var(pChildren[1]) );
            pFans[2] = If_DsdVecObj( p->vObjs, Abc_Lit2Var(pChildren[2]) );
            nSSize = pFans[0]->nSupp + pFans[1]->nSupp + pFans[2]->nSupp;
            for ( j = k = 0; k < If_DsdObjSuppSize(pFans[0]); k++ )
                pPermNew[j++] = pPerm[k];
            for ( k = 0; k < If_DsdObjSuppSize(pFans[2]); k++ )
                pPermNew[j++] = pPerm[pFans[0]->nSupp + pFans[1]->nSupp + k];
            for ( k = 0; k < If_DsdObjSuppSize(pFans[1]); k++ )
                pPermNew[j++] = pPerm[pFans[0]->nSupp + k];
            assert( j == nSSize );
            for ( j = 0; j < nSSize; j++ )
                pPerm[j] = pPermNew[j];
        }
        if ( Abc_LitIsCompl(pChildren[1]) )
        {
            pChildren[1] = Abc_LitNot(pChildren[1]);
            pChildren[2] = Abc_LitNot(pChildren[2]);
            fCompl ^= 1;
        }
    }
    else if ( Type == IF_DSD_PRIME )
    {
        char pCanonPerm[DAU_MAX_VAR];
        int i, uCanonPhase, pFirsts[DAU_MAX_VAR];
        uCanonPhase = Abc_TtCanonicize( pTruth, nLits, pCanonPerm );
        fCompl = ((uCanonPhase >> nLits) & 1);
        for ( i = 0; i < nLits; i++ )
        {
            pFirsts[i] = nSSize;
            nSSize += If_DsdVecLitSuppSize(p->vObjs, pLits[i]);
        }
        for ( j = i = 0; i < nLits; i++ )
        {
            int iLitNew = Abc_LitNotCond( pLits[(int)pCanonPerm[i]], ((uCanonPhase>>i)&1) );
            pFanin = If_DsdVecObj( p->vObjs, Abc_Lit2Var(iLitNew) );
            fComplFan = If_DsdObjIsVar(pFanin) && Abc_LitIsCompl(iLitNew);
            pChildren[nChildren++] = Abc_LitNotCond( iLitNew, fComplFan );
            for ( k = 0; k < (int)pFanin->nSupp; k++ )            
                pPermNew[j++] = (unsigned char)Abc_LitNotCond( (int)pPerm[pFirsts[(int)pCanonPerm[i]] + k], fComplFan );
        }
        assert( j == nSSize );
        for ( j = 0; j < nSSize; j++ )
            pPerm[j] = pPermNew[j];
        Abc_TtStretch6( pTruth, nLits, p->nVars );
    }
    else assert( 0 );
    // create new graph
    Id = If_DsdObjFindOrAdd( p, Type, pChildren, nChildren, pTruth );
    return Abc_Var2Lit( Id, fCompl );
}

/**Function*************************************************************

  Synopsis    [Creating DSD network from SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void If_DsdMergeMatches( char * pDsd, int * pMatches )
{
    int pNested[DAU_MAX_VAR];
    int i, nNested = 0;
    for ( i = 0; pDsd[i]; i++ )
    {
        pMatches[i] = 0;
        if ( pDsd[i] == '(' || pDsd[i] == '[' || pDsd[i] == '<' || pDsd[i] == '{' )
            pNested[nNested++] = i;
        else if ( pDsd[i] == ')' || pDsd[i] == ']' || pDsd[i] == '>' || pDsd[i] == '}' )
            pMatches[pNested[--nNested]] = i;
        assert( nNested < DAU_MAX_VAR );
    }
    assert( nNested == 0 );
}
int If_DsdManAddDsd_rec( char * pStr, char ** p, int * pMatches, If_DsdMan_t * pMan, word * pTruth, unsigned char * pPerm, int * pnSupp )
{
    unsigned char * pPermStart = pPerm + *pnSupp;
    int iRes = -1, fCompl = 0;
    if ( **p == '!' )
    {
        fCompl = 1;
        (*p)++;
    }
    assert( !((**p >= 'A' && **p <= 'F') || (**p >= '0' && **p <= '9')) );
    if ( **p >= 'a' && **p <= 'z' ) // var
    {
        pPerm[(*pnSupp)++] = Abc_Var2Lit( **p - 'a', fCompl );
        return 2;
    }
    if ( **p == '(' || **p == '[' || **p == '<' || **p == '{' ) // and/or/xor
    {
        int Type, nLits = 0, pLits[DAU_MAX_VAR];
        char * q = pStr + pMatches[ *p - pStr ];
        if ( **p == '(' )
            Type = DAU_DSD_AND;
        else if ( **p == '[' )
            Type = DAU_DSD_XOR;
        else if ( **p == '<' )
            Type = DAU_DSD_MUX;
        else if ( **p == '{' )
            Type = DAU_DSD_PRIME;
        else assert( 0 );
        assert( *q == **p + 1 + (**p != '(') );
        for ( (*p)++; *p < q; (*p)++ )
            pLits[nLits++] = If_DsdManAddDsd_rec( pStr, p, pMatches, pMan, pTruth, pPerm, pnSupp );
        assert( *p == q );
        iRes = If_DsdManOperation( pMan, Type, pLits, nLits, pPermStart, pTruth );
        return Abc_LitNotCond( iRes, fCompl );
    }
    assert( 0 );
    return -1;
}
int If_DsdManAddDsd( If_DsdMan_t * p, char * pDsd, word * pTruth, unsigned char * pPerm, int * pnSupp )
{
    int iRes = -1, fCompl = 0;
    if ( *pDsd == '!' )
         pDsd++, fCompl = 1;
    if ( Dau_DsdIsConst0(pDsd) )
        iRes = 0;
    else if ( Dau_DsdIsConst1(pDsd) )
        iRes = 1;
    else if ( Dau_DsdIsVar(pDsd) )
    {
        pPerm[(*pnSupp)++] = Dau_DsdReadVar(pDsd);
        iRes = 2;
    }
    else
    {
        int pMatches[DAU_MAX_STR];
        If_DsdMergeMatches( pDsd, pMatches );
        iRes = If_DsdManAddDsd_rec( pDsd, &pDsd, pMatches, p, pTruth, pPerm, pnSupp );
    }
    return Abc_LitNotCond( iRes, fCompl );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if XY-decomposability holds to this LUT size.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
// collect supports of the node
void If_DsdManGetSuppSizes( If_DsdMan_t * p, If_DsdObj_t * pObj, int * pSSizes )
{
    If_DsdObj_t * pFanin; int i;
    If_DsdObjForEachFanin( p->vObjs, pObj, pFanin, i )
        pSSizes[i] = If_DsdObjSuppSize(pFanin);    
}
// checks if there is a way to package some fanins 
int If_DsdManCheckAndXor( If_DsdMan_t * p, If_DsdObj_t * pObj, int nSuppAll, int LutSize )
{
    int i[6], LimitOut, SizeIn, SizeOut, pSSizes[DAU_MAX_VAR];
    int nFans = If_DsdObjFaninNum(pObj);
    assert( pObj->nFans > 2 );
    assert( If_DsdObjSuppSize(pObj) > LutSize );
    If_DsdManGetSuppSizes( p, pObj, pSSizes );
    LimitOut = LutSize - (nSuppAll - pObj->nSupp + 1);
    assert( LimitOut < LutSize );
    for ( i[0] = 0;      i[0] < nFans; i[0]++ )
    for ( i[1] = i[0]+1; i[1] < nFans; i[1]++ )
    {
        SizeIn = pSSizes[i[0]] + pSSizes[i[1]];
        SizeOut = pObj->nSupp - SizeIn;
        if ( SizeIn > LutSize || SizeOut > LimitOut )
            continue;
        return (1 << i[0]) | (1 << i[1]);
    }
    if ( pObj->nFans == 3 )
        return 0;
    for ( i[0] = 0;      i[0] < nFans; i[0]++ )
    for ( i[1] = i[0]+1; i[1] < nFans; i[1]++ )
    for ( i[2] = i[1]+1; i[2] < nFans; i[2]++ )
    {
        SizeIn = pSSizes[i[0]] + pSSizes[i[1]] + pSSizes[i[2]];
        SizeOut = pObj->nSupp - SizeIn;
        if ( SizeIn > LutSize || SizeOut > LimitOut )
            continue;
        return (1 << i[0]) | (1 << i[1]) | (1 << i[2]);
    }
    return 0;
}
// checks if there is a way to package some fanins 
int If_DsdManCheckPrime( If_DsdMan_t * p, If_DsdObj_t * pObj, int nSuppAll, int LutSize )
{
    int fVerbose = 0;
    int i, v, set, LimitOut, SizeIn, SizeOut, pSSizes[DAU_MAX_VAR];
    int truthId = If_DsdObjTruthId( p, pObj );
    int nFans = If_DsdObjFaninNum(pObj);
    Vec_Int_t * vSets = (Vec_Int_t *)Vec_PtrEntry(p->vTtDecs, truthId);
if ( fVerbose )
printf( "\n" );
if ( fVerbose )
Dau_DecPrintSets( vSets, nFans );
    assert( pObj->nFans > 2 );
    assert( If_DsdObjSuppSize(pObj) > LutSize );
    If_DsdManGetSuppSizes( p, pObj, pSSizes );
    LimitOut = LutSize - (nSuppAll - pObj->nSupp + 1);
    assert( LimitOut < LutSize );
    Vec_IntForEachEntry( vSets, set, i )
    {
        SizeIn = SizeOut = 0;
        for ( v = 0; v < nFans; v++ )
        {
            int Value = ((set >> (v << 1)) & 3);
            if ( Value == 0 )
                SizeOut += pSSizes[v];
            else if ( Value == 1 )
                SizeIn += pSSizes[v];
            else if ( Value == 3 )
            {
                SizeIn += pSSizes[v];
                SizeOut += pSSizes[v];
            }
            else assert( Value == 0 );
            if ( SizeIn > LutSize || SizeOut > LimitOut )
                break;
        }
        if ( v == nFans )
            return set;
    }
    return 0;
}
int If_DsdManCheckXY( If_DsdMan_t * p, int iDsd, int LutSize )
{
    int fVerbose = 0;
    If_DsdObj_t * pObj, * pTemp; int i, Mask;
    pObj = If_DsdVecObj( p->vObjs, Abc_Lit2Var(iDsd) );
    if ( fVerbose )
    If_DsdManPrintOne( stdout, p, Abc_Lit2Var(iDsd), NULL, 0 );
    if ( If_DsdObjSuppSize(pObj) <= LutSize )
    {
        if ( fVerbose )
        printf( "    Trivial\n" );
        return 1;
    }
    If_DsdManCollect( p, pObj->Id, p->vNodes );
    If_DsdVecForEachObjVec( p->vNodes, p->vObjs, pTemp, i )
        if ( If_DsdObjSuppSize(pTemp) <= LutSize && If_DsdObjSuppSize(pObj) - If_DsdObjSuppSize(pTemp) <= LutSize - 1 )
        {
            if ( fVerbose )
            printf( "    Dec using node " );
            if ( fVerbose )
            If_DsdManPrintOne( stdout, p, pTemp->Id, NULL, 1 );
            return 1;
        }
    If_DsdVecForEachObjVec( p->vNodes, p->vObjs, pTemp, i )
        if ( (If_DsdObjType(pTemp) == IF_DSD_AND || If_DsdObjType(pTemp) == IF_DSD_XOR) && If_DsdObjFaninNum(pTemp) > 2 && If_DsdObjSuppSize(pTemp) > LutSize )
        {
            if ( (Mask = If_DsdManCheckAndXor(p, pTemp, If_DsdObjSuppSize(pObj), LutSize)) )
            {
                if ( fVerbose )
                printf( "    " );
                if ( fVerbose )
                Abc_TtPrintBinary( (word *)&Mask, 4 ); 
                if ( fVerbose )
                printf( "    Using multi-input AND/XOR node\n" );
                return 1;
            }
        }
    If_DsdVecForEachObjVec( p->vNodes, p->vObjs, pTemp, i )
        if ( If_DsdObjType(pTemp) == IF_DSD_PRIME )
        {
            if ( (Mask = If_DsdManCheckPrime(p, pTemp, If_DsdObjSuppSize(pObj), LutSize)) )
            {
                if ( fVerbose )
                printf( "    " );
                if ( fVerbose )
                Dau_DecPrintSet( Mask, If_DsdObjFaninNum(pTemp), 0 );
                if ( fVerbose )
                printf( "    Using prime node\n" );
                return 1;
            }
        }
    if ( fVerbose )
    printf( "    UNDEC\n" );
    return 0;
}
int If_DsdManCheckXYZ( If_DsdMan_t * p, int iDsd, int LutSize ) 
{
    return 1;
}

/**Function*************************************************************

  Synopsis    [Add the function to the DSD manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int If_DsdManCompute( If_DsdMan_t * p, word * pTruth, int nLeaves, unsigned char * pPerm, char * pLutStruct )
{
    word pCopy[DAU_MAX_WORD], * pRes;
    char pDsd[DAU_MAX_STR];
    int iDsd, nSizeNonDec, nSupp = 0;
    assert( nLeaves <= DAU_MAX_VAR );
    Abc_TtCopy( pCopy, pTruth, p->nWords, 0 );
    nSizeNonDec = Dau_DsdDecompose( pCopy, nLeaves, 0, 0, pDsd );
    if ( !strcmp(pDsd, "(![(!e!d)c]!(b!a))") )
    {
//        int x = 0;
    }
    if ( nSizeNonDec > 0 )
        Abc_TtStretch6( pCopy, nSizeNonDec, p->nVars );
    memset( pPerm, 0xFF, nLeaves );
    iDsd = If_DsdManAddDsd( p, pDsd, pCopy, pPerm, &nSupp );
    assert( nSupp == nLeaves );
    // verify the result
    pRes = If_DsdManComputeTruth( p, iDsd, pPerm );
    if ( !Abc_TtEqual(pRes, pTruth, p->nWords) )
    {
//        If_DsdManPrint( p, NULL );
        printf( "\n" );
        printf( "Verification failed!\n" );
        Dau_DsdPrintFromTruth( pTruth, nLeaves );
        Dau_DsdPrintFromTruth( pRes, nLeaves );
        If_DsdManPrintOne( stdout, p, Abc_Lit2Var(iDsd), pPerm, 1 );
        printf( "\n" );
    }
    If_DsdVecObjIncRef( p->vObjs, Abc_Lit2Var(iDsd) );
    if ( pLutStruct )
    {
        int LutSize = (int)(pLutStruct[0] - '0');
        assert( pLutStruct[2] == 0 );
        if ( If_DsdManCheckXY( p, iDsd, LutSize ) )
            If_DsdVecObjSetMark( p->vObjs, Abc_Lit2Var(iDsd) );
    }
    return iDsd;
}
int If_DsdManCheckDec( If_DsdMan_t * p, int iDsd )
{
    return If_DsdVecObjMark( p->vObjs, Abc_Lit2Var(iDsd) );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

