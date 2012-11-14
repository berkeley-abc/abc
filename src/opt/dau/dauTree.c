/**CFile****************************************************************

  FileName    [dauTree.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware unmapping.]

  Synopsis    [Canonical DSD package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: dauTree.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dauInt.h"
#include "misc/mem/mem.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Dss_Obj_t_ Dss_Obj_t;
struct Dss_Obj_t_
{
    unsigned       Id;             // node ID
    unsigned       Next;           // next node
    unsigned       Mirror  :  30;  // node ID
    unsigned       fMark0  :   1;  // user mark
    unsigned       fMark1  :   1;  // user mark
    unsigned       iVar    :   8;  // variable
    unsigned       nSupp   :   8;  // variable
    unsigned       Data    :   8;  // variable
    unsigned       Type    :   3;  // node type
    unsigned       nFans   :   5;  // fanin count
    unsigned       pFans[0];       // fanins
};

typedef struct Dss_Ntk_t_ Dss_Ntk_t;
struct Dss_Ntk_t_
{
    int            nVars;          // the number of variables
    int            nMem;           // memory used
    int            nMemAlloc;      // memory allocated
    Dss_Obj_t *    pMem;           // memory array
    Dss_Obj_t *    pRoot;          // root node
    Vec_Ptr_t *    vObjs;          // internal nodes
};

struct Dss_Man_t_
{
    int            nVars;          // variable number
    int            nBins;          // table size
    unsigned *     pBins;          // hash table
    Mem_Flex_t *   pMem;           // memory for nodes
    Vec_Ptr_t *    vObjs;          // objects
    Vec_Int_t *    vLeaves;        // temp
};

static inline Dss_Obj_t *  Dss_Regular( Dss_Obj_t * p )                            { return (Dss_Obj_t *)((ABC_PTRUINT_T)(p) & ~01);                                    }
static inline Dss_Obj_t *  Dss_Not( Dss_Obj_t * p )                                { return (Dss_Obj_t *)((ABC_PTRUINT_T)(p) ^  01);                                    }
static inline Dss_Obj_t *  Dss_NotCond( Dss_Obj_t * p, int c )                     { return (Dss_Obj_t *)((ABC_PTRUINT_T)(p) ^ (c));                                    }
static inline int          Dss_IsComplement( Dss_Obj_t * p )                       { return (int)((ABC_PTRUINT_T)(p) & 01);                                             }

static inline void         Dss_ObjClean( Dss_Obj_t * pObj )                        { memset( pObj, 0, sizeof(Dss_Obj_t) );                                              }
static inline int          Dss_ObjId( Dss_Obj_t * pObj )                           { return pObj->Id;                                                                   }
static inline int          Dss_ObjType( Dss_Obj_t * pObj )                         { return pObj->Type;                                                                 }
static inline int          Dss_ObjFaninNum( Dss_Obj_t * pObj )                     { return pObj->nFans;                                                                }
static inline int          Dss_ObjFaninC( Dss_Obj_t * pObj, int i )                { assert(i < (int)pObj->nFans); return Abc_LitIsCompl(pObj->pFans[i]);               }
static inline word *       Dss_ObjTruth( Dss_Obj_t * pObj )                        { return (word *)(pObj->pFans + pObj->nFans + (pObj->nFans & 1));                    }

static inline Dss_Obj_t *  Dss_NtkObj( Dss_Ntk_t * p, int Id )                     { return (Dss_Obj_t *)Vec_PtrEntry(p->vObjs, Id);                                    }
static inline Dss_Obj_t *  Dss_NtkConst0( Dss_Ntk_t * p )                          { return Dss_NtkObj( p, 0 );                                                         }
static inline Dss_Obj_t *  Dss_NtkVar( Dss_Ntk_t * p, int v )                      { assert( v >= 0 && v < p->nVars ); return Dss_NtkObj( p, v+1 );                     }

static inline Dss_Obj_t *  Dss_Lit2ObjNtk( Dss_Ntk_t * p, int iLit )               { return Dss_NotCond(Dss_NtkObj(p, Abc_Lit2Var(iLit)), Abc_LitIsCompl(iLit));        }
static inline Dss_Obj_t *  Dss_ObjFaninNtk( Dss_Ntk_t * p, Dss_Obj_t * pObj,int i) { assert(i < (int)pObj->nFans); return Dss_NtkObj( p, Abc_Lit2Var(pObj->pFans[i]) ); }
static inline Dss_Obj_t *  Dss_ObjChildNtk( Dss_Ntk_t * p, Dss_Obj_t * pObj,int i) { assert(i < (int)pObj->nFans); return Dss_Lit2ObjNtk(p, pObj->pFans[i]);            }

static inline Dss_Obj_t *  Dss_ManObj( Dss_Man_t * p, int Id )                     { return (Dss_Obj_t *)Vec_PtrEntry(p->vObjs, Id);                                    }
static inline Dss_Obj_t *  Dss_ManConst0( Dss_Man_t * p )                          { return Dss_ManObj( p, 0 );                                                         }
static inline Dss_Obj_t *  Dss_ManVar( Dss_Man_t * p, int v )                      { assert( v >= 0 && v < p->nVars ); return Dss_ManObj( p, v+1 );                     }

static inline int          Dss_Obj2Lit( Dss_Obj_t * pObj )                         { return Abc_Var2Lit(Dss_Regular(pObj)->Id, Dss_IsComplement(pObj));                 }
static inline Dss_Obj_t *  Dss_Lit2Obj( Dss_Man_t * p, int iLit )                  { return Dss_NotCond(Dss_ManObj(p, Abc_Lit2Var(iLit)), Abc_LitIsCompl(iLit));        }
static inline Dss_Obj_t *  Dss_ObjFanin( Dss_Man_t * p, Dss_Obj_t * pObj, int i )  { assert(i < (int)pObj->nFans); return Dss_ManObj(p, Abc_Lit2Var(pObj->pFans[i]));   }
static inline Dss_Obj_t *  Dss_ObjChild( Dss_Man_t * p, Dss_Obj_t * pObj, int i )  { assert(i < (int)pObj->nFans); return Dss_Lit2Obj(p, pObj->pFans[i]);               }

#define Dss_NtkForEachNode( p, pObj, i )                        \
    Vec_PtrForEachEntryStart( Dss_Obj_t *, p->vObjs, pObj, i, p->nVars + 1 )
#define Dss_ObjForEachFaninNtk( p, pObj, pFanin, i )            \
    for ( i = 0; (i < Dss_ObjFaninNum(pObj)) && ((pFanin) = Dss_ObjFaninNtk(p, pObj, i)); i++ )
#define Dss_ObjForEachChildNtk( p, pObj, pFanin, i )            \
    for ( i = 0; (i < Dss_ObjFaninNum(pObj)) && ((pFanin) = Dss_ObjChildNtk(p, pObj, i)); i++ )

#define Dss_ManForEachObjVec( vLits, p, pObj, i )               \
    for ( i = 0; (i < Vec_IntSize(vLits)) && ((pObj) = Dss_Lit2Obj(p, Vec_IntEntry(vLits,i))); i++ )
#define Dss_ObjForEachFanin( p, pObj, pFanin, i )               \
    for ( i = 0; (i < Dss_ObjFaninNum(pObj)) && ((pFanin) = Dss_ObjFanin(p, pObj, i)); i++ )
#define Dss_ObjForEachChild( p, pObj, pFanin, i )               \
    for ( i = 0; (i < Dss_ObjFaninNum(pObj)) && ((pFanin) = Dss_ObjChild(p, pObj, i)); i++ )


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
 
/**Function*************************************************************

  Synopsis    [Creating DSD network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dss_Obj_t * Dss_ObjAllocNtk( Dss_Ntk_t * p, int Type, int nFans, int nTruthVars )
{
    int nStructs = 1 + (nFans / sizeof(Dss_Obj_t)) + (nFans % sizeof(Dss_Obj_t) > 0);
    Dss_Obj_t * pObj = p->pMem + p->nMem;
    p->nMem += nStructs;
    assert( p->nMem < p->nMemAlloc );
    Dss_ObjClean( pObj );
    pObj->Type   = Type;
    pObj->nFans  = nFans;
    pObj->Id     = Vec_PtrSize( p->vObjs );
    pObj->iVar   = 31;
    pObj->Mirror = ~0;
    Vec_PtrPush( p->vObjs, pObj );
    return pObj;
}
Dss_Obj_t * Dss_ObjCreateNtk( Dss_Ntk_t * p, int Type, Vec_Int_t * vFaninLits )
{
    Dss_Obj_t * pObj;
    int i, Entry;
    pObj = Dss_ObjAllocNtk( p, Type, Vec_IntSize(vFaninLits), 0 );
    Vec_IntForEachEntry( vFaninLits, Entry, i )
    {
        pObj->pFans[i] = Entry;
        pObj->nSupp += Dss_ObjFaninNtk(p, pObj, i)->nSupp;
    }
    assert( i == (int)pObj->nFans );
    return pObj;
}
Dss_Ntk_t * Dss_NtkAlloc( int nVars )
{
    Dss_Ntk_t * p;
    Dss_Obj_t * pObj;
    int i;
    p = ABC_CALLOC( Dss_Ntk_t, 1 );
    p->nVars     = nVars;
    p->nMemAlloc = DAU_MAX_STR;
    p->pMem      = ABC_ALLOC( Dss_Obj_t, p->nMemAlloc );
    p->vObjs     = Vec_PtrAlloc( 100 );
    Dss_ObjAllocNtk( p, DAU_DSD_CONST0, 0, 0 );
    for ( i = 0; i < nVars; i++ )
    {
        pObj = Dss_ObjAllocNtk( p, DAU_DSD_VAR, 0, 0 );
        pObj->iVar = i;
        pObj->nSupp = 1;
    }
    return p;
}
void Dss_NtkFree( Dss_Ntk_t * p )
{
    Vec_PtrFree( p->vObjs );
    ABC_FREE( p->pMem );
    ABC_FREE( p );
}
void Dss_NtkPrint_rec( Dss_Ntk_t * p, Dss_Obj_t * pObj )
{
    char OpenType[7]  = {0, 0, 0, '(', '[', '<', '{'};
    char CloseType[7] = {0, 0, 0, ')', ']', '>', '}'};
    Dss_Obj_t * pFanin;
    int i;
    assert( !Dss_IsComplement(pObj) );
    if ( pObj->Type == DAU_DSD_VAR )
        { printf( "%c", 'a' + pObj->iVar ); return; }
    printf( "%c", OpenType[pObj->Type] );
    Dss_ObjForEachFaninNtk( p, pObj, pFanin, i )
    {
        printf( "%s", Dss_ObjFaninC(pObj, i) ? "!":"" );
        Dss_NtkPrint_rec( p, pFanin );
    }
    printf( "%c", CloseType[pObj->Type] );
}
void Dss_NtkPrint( Dss_Ntk_t * p )
{
    if ( Dss_Regular(p->pRoot)->Type == DAU_DSD_CONST0 )
        printf( "%d", Dss_IsComplement(p->pRoot) );
    else
    {
        printf( "%s", Dss_IsComplement(p->pRoot) ? "!":"" );        
        if ( Dss_Regular(p->pRoot)->Type == DAU_DSD_VAR )
            printf( "%c", 'a' + Dss_Regular(p->pRoot)->iVar );
        else
            Dss_NtkPrint_rec( p, Dss_Regular(p->pRoot) );
    }
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    [Creating DSD network from SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Dau_DsdMergeMatches( char * pDsd, int * pMatches )
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
int Dss_NtkCreate_rec( char * pStr, char ** p, int * pMatches, Dss_Ntk_t * pNtk )
{
    int fCompl = 0;
    if ( **p == '!' )
    {
        fCompl = 1;
        (*p)++;
    }
    while ( (**p >= 'A' && **p <= 'F') || (**p >= '0' && **p <= '9') )
        (*p)++;
    if ( **p == '<' )
    {
        char * q = pStr + pMatches[ *p - pStr ];
        if ( *(q+1) == '{' )
            *p = q+1;
    }
    if ( **p >= 'a' && **p <= 'z' ) // var
        return Abc_Var2Lit( Dss_ObjId(Dss_NtkVar(pNtk, **p - 'a')), fCompl );
    if ( **p == '(' || **p == '[' || **p == '<' || **p == '{' ) // and/or/xor
    {
        Dss_Obj_t * pObj;
        Vec_Int_t * vFaninLits = Vec_IntAlloc( 10 );
        char * q = pStr + pMatches[ *p - pStr ];
        int Type;
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
            Vec_IntPush( vFaninLits, Dss_NtkCreate_rec(pStr, p, pMatches, pNtk) );
        assert( *p == q );
        pObj = Dss_ObjCreateNtk( pNtk, Type, vFaninLits );
        Vec_IntFree( vFaninLits );
        return Abc_LitNotCond( Dss_Obj2Lit(pObj), fCompl );
    }
    assert( 0 );
    return -1;
}
Dss_Ntk_t * Dss_NtkCreate( char * pDsd, int nVars )
{
    int fCompl = 0;
    Dss_Ntk_t * pNtk = Dss_NtkAlloc( nVars );
    if ( *pDsd == '!' )
         pDsd++, fCompl = 1;
    if ( Dau_DsdIsConst(pDsd) )
        pNtk->pRoot = Dss_NtkConst0(pNtk);
    else if ( Dau_DsdIsVar(pDsd) )
        pNtk->pRoot = Dss_NtkVar(pNtk, Dau_DsdReadVar(pDsd));
    else
    {
        int iLit, pMatches[DAU_MAX_STR];
        Dau_DsdMergeMatches( pDsd, pMatches );
        iLit = Dss_NtkCreate_rec( pDsd, &pDsd, pMatches, pNtk );
        pNtk->pRoot = Dss_Lit2ObjNtk( pNtk, iLit );
    }
    if ( fCompl )
        pNtk->pRoot = Dss_Not(pNtk->pRoot);
    return pNtk;
}
 

/**Function*************************************************************

  Synopsis    [Comparing two DSD nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dss_ObjCompareNtk( Dss_Ntk_t * p, Dss_Obj_t * p0i, Dss_Obj_t * p1i )
{
    Dss_Obj_t * p0 = Dss_Regular(p0i);
    Dss_Obj_t * p1 = Dss_Regular(p1i);
    Dss_Obj_t * pChild0, * pChild1;
    int i, Res;
    if ( Dss_ObjType(p0) < Dss_ObjType(p1) )
        return -1;
    if ( Dss_ObjType(p0) > Dss_ObjType(p1) )
        return 1;
    if ( Dss_ObjType(p0) < DAU_DSD_AND )
        return 0;
    if ( Dss_ObjFaninNum(p0) < Dss_ObjFaninNum(p1) )
        return -1;
    if ( Dss_ObjFaninNum(p0) > Dss_ObjFaninNum(p1) )
        return 1;
    for ( i = 0; i < Dss_ObjFaninNum(p0); i++ )
    {
        pChild0 = Dss_ObjChildNtk( p, p0, i );
        pChild1 = Dss_ObjChildNtk( p, p1, i );
        Res = Dss_ObjCompareNtk( p, pChild0, pChild1 );
        if ( Res != 0 )
            return Res;
    }
    if ( Dss_IsComplement(p0i) < Dss_IsComplement(p1i) )
        return -1;
    if ( Dss_IsComplement(p0i) > Dss_IsComplement(p1i) )
        return 1;
    return 0;
}
void Dss_ObjSortNtk( Dss_Ntk_t * p, Dss_Obj_t ** pNodes, int nNodes )
{
    int i, j, best_i;
    for ( i = 0; i < nNodes-1; i++ )
    {
        best_i = i;
        for ( j = i+1; j < nNodes; j++ )
            if ( Dss_ObjCompareNtk(p, pNodes[best_i], pNodes[j]) == 1 )
                best_i = j;
        if ( i == best_i )
            continue;
        ABC_SWAP( Dss_Obj_t *, pNodes[i], pNodes[best_i] );
    }
}

/**Function*************************************************************

  Synopsis    [Creating DSD network from SOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dss_NtkCheck( Dss_Ntk_t * p )
{
    Dss_Obj_t * pObj, * pFanin;
    int i, k;
    Dss_NtkForEachNode( p, pObj, i )
    {
        Dss_ObjForEachFaninNtk( p, pObj, pFanin, k )
        {
            if ( pObj->Type == DAU_DSD_AND && pFanin->Type == DAU_DSD_AND )
                assert( Dss_ObjFaninC(pObj, k) );
            else if ( pObj->Type == DAU_DSD_XOR )
                assert( pFanin->Type != DAU_DSD_XOR );
            else if ( pObj->Type == DAU_DSD_MUX )
                assert( !Dss_ObjFaninC(pObj, 0) );
        }
    }
}
void Dss_NtkTransform( Dss_Ntk_t * p )
{
    Dss_Obj_t * pChildren[DAU_MAX_VAR];
    Dss_Obj_t * pObj, * pChild;
    int i, k;
    Dss_NtkForEachNode( p, pObj, i )
    {
        Dss_ObjForEachChildNtk( p, pObj, pChild, k )
            pChildren[k] = pChild;
        Dss_ObjSortNtk( p, pChildren, Dss_ObjFaninNum(pObj) );
        for ( k = 0; k < Dss_ObjFaninNum(pObj); k++ )
            pObj->pFans[k] = Dss_Obj2Lit( pChildren[k] );
    }
}

/**Function*************************************************************

  Synopsis    [Comparing two DSD nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dss_ObjCompare( Dss_Man_t * p, Dss_Obj_t * p0i, Dss_Obj_t * p1i )
{
    Dss_Obj_t * p0 = Dss_Regular(p0i);
    Dss_Obj_t * p1 = Dss_Regular(p1i);
    Dss_Obj_t * pChild0, * pChild1;
    int i, Res;
    if ( Dss_ObjType(p0) < Dss_ObjType(p1) )
        return -1;
    if ( Dss_ObjType(p0) > Dss_ObjType(p1) )
        return 1;
    if ( Dss_ObjType(p0) < DAU_DSD_AND )
    {
        assert( !Dss_IsComplement(p0i) );
        assert( !Dss_IsComplement(p1i) );
        return 0;
    }
    if ( Dss_ObjFaninNum(p0) < Dss_ObjFaninNum(p1) )
        return -1;
    if ( Dss_ObjFaninNum(p0) > Dss_ObjFaninNum(p1) )
        return 1;
    for ( i = 0; i < Dss_ObjFaninNum(p0); i++ )
    {
        pChild0 = Dss_ObjChild( p, p0, i );
        pChild1 = Dss_ObjChild( p, p1, i );
        Res = Dss_ObjCompare( p, pChild0, pChild1 );
        if ( Res != 0 )
            return Res;
    }
    if ( Dss_IsComplement(p0i) < Dss_IsComplement(p1i) )
        return -1;
    if ( Dss_IsComplement(p0i) > Dss_IsComplement(p1i) )
        return 1;
    return 0;
}
void Dss_ObjSort( Dss_Man_t * p, Dss_Obj_t ** pNodes, int nNodes )
{
    int i, j, best_i;
    for ( i = 0; i < nNodes-1; i++ )
    {
        best_i = i;
        for ( j = i+1; j < nNodes; j++ )
            if ( Dss_ObjCompare(p, pNodes[best_i], pNodes[j]) == 1 )
                best_i = j;
        if ( i == best_i )
            continue;
        ABC_SWAP( Dss_Obj_t *, pNodes[i], pNodes[best_i] );
    }
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dss_Obj_t * Dss_ObjAlloc( Dss_Man_t * p, int Type, int nFans, int nTruthVars )
{
    int nInts = sizeof(Dss_Obj_t) / sizeof(int) + nFans;
    int nWords = (nInts >> 1) + (nInts & 1) + (nTruthVars ? Abc_Truth6WordNum(nTruthVars) : 0);
    Dss_Obj_t * pObj = (Dss_Obj_t *)Mem_FlexEntryFetch( p->pMem, sizeof(word) * nWords );
    Dss_ObjClean( pObj );
    pObj->Type   = Type;
    pObj->nFans  = nFans;
    pObj->Id     = Vec_PtrSize( p->vObjs );
    pObj->iVar   = 31;
    pObj->Mirror = ~0;
    Vec_PtrPush( p->vObjs, pObj );
    return pObj;
}
Dss_Obj_t * Dss_ObjCreate( Dss_Man_t * p, int Type, Vec_Int_t * vFaninLits )
{
    Dss_Obj_t * pObj, * pFanin, * pPrev = NULL;
    int i, Entry;
    // check that leaves are in good order
    Dss_ManForEachObjVec( vFaninLits, p, pFanin, i )
    {
        assert( pPrev == NULL || Dss_ObjCompare(p, pPrev, pFanin) <= 0 );
        pPrev = pFanin;
    }
    // create new node
    pObj = Dss_ObjAlloc( p, Type, Vec_IntSize(vFaninLits), 0 );
    Vec_IntForEachEntry( vFaninLits, Entry, i )
    {
        pObj->pFans[i] = Entry;
        pObj->nSupp += Dss_ObjFanin(p, pObj, i)->nSupp;
    }
    return pObj;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned Dss_ObjHashKey( Dss_Man_t * p, int Type, Vec_Int_t * vFaninLits )
{
    static int s_Primes[8] = { 1699, 4177, 5147, 5647, 6343, 7103, 7873, 8147 };
    int i, Entry;
    unsigned uHash = Type * 7873 + Vec_IntSize(vFaninLits) * 8147;
    Vec_IntForEachEntry( vFaninLits, Entry, i )
        uHash += Entry * s_Primes[i & 0x7];
    return uHash % p->nBins;
}
unsigned * Dss_ObjHashLookup( Dss_Man_t * p, int Type, Vec_Int_t * vFaninLits )
{
    Dss_Obj_t * pObj;
    unsigned * pSpot = p->pBins + Dss_ObjHashKey(p, Type, vFaninLits);
    for ( ; *pSpot; pSpot = &pObj->Next )
    {
        pObj = Dss_ManObj( p, *pSpot );
        if ( (int)pObj->Type == Type && (int)pObj->nFans == Vec_IntSize(vFaninLits) && !memcmp(pObj->pFans, Vec_IntArray(vFaninLits), sizeof(int)*pObj->nFans) ) // equal
            return pSpot;
    }
    return pSpot;
}
Dss_Obj_t * Dss_ObjFindOrAdd( Dss_Man_t * p, int Type, Vec_Int_t * vFaninLits )
{
    Dss_Obj_t * pObj;
    unsigned * pSpot = Dss_ObjHashLookup( p, Type, vFaninLits );
    if ( *pSpot )
        return Dss_ManObj( p, *pSpot );
    pObj = Dss_ObjCreate( p, Type, vFaninLits );
    *pSpot = pObj->Id;
    return pObj;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dss_Man_t * Dss_ManAlloc( int nVars )
{
    Dss_Man_t * p;
    Dss_Obj_t * pObj;
    int i;
    p = ABC_CALLOC( Dss_Man_t, 1 );
    p->nVars = nVars;
    p->nBins = Abc_PrimeCudd( 1000 );
    p->pBins = ABC_CALLOC( unsigned, p->nBins );
    p->pMem  = Mem_FlexStart();
    p->vObjs = Vec_PtrAlloc( 1000 );
    Dss_ObjAlloc( p, DAU_DSD_CONST0, 0, 0 );
    for ( i = 0; i < nVars; i++ )
    {
        pObj = Dss_ObjAlloc( p, DAU_DSD_VAR, 0, 0 );
        pObj->iVar = i;
        pObj->nSupp = 1;
        pObj->Mirror = 1;
    }
    p->vLeaves = Vec_IntAlloc( 32 );
    return p;

}
void Dss_ManFree( Dss_Man_t * p )
{
    Vec_IntFreeP( &p->vLeaves );
    Vec_PtrFreeP( &p->vObjs );
    Mem_FlexStop( p->pMem, 0 );
    ABC_FREE( p->pBins );
    ABC_FREE( p );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dss_Obj_t * Dss_ManShiftTree( Dss_Man_t * p, Dss_Obj_t * pObj, int Shift )
{
    Vec_Int_t * vFaninLits;
    Dss_Obj_t * pFanin, * pObjNew;
    int i;
    assert( !Dss_IsComplement(pObj) );
    assert( pObj->Mirror == pObj->Id );
    if ( pObj->Type == DAU_DSD_VAR )
    {
        assert( (int)pObj->iVar + Shift < p->nVars );
        return Dss_ManVar( p, pObj->iVar + Shift );
    }
    // collect fanins
    vFaninLits = Vec_IntAlloc( 10 );
    Dss_ObjForEachFanin( p, pObj, pFanin, i )
    {
        pFanin = Dss_ManShiftTree( p, pFanin, Shift );
        Vec_IntPush( vFaninLits, Abc_Var2Lit(pFanin->Id, Dss_ObjFaninC(pObj, i)) );
    }
    // create new graph
    pObjNew = Dss_ObjFindOrAdd( p, pObj->Type, vFaninLits );
    pObjNew->Mirror = pObj->Id;
    Vec_IntFree( vFaninLits );
    return pObjNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dss_ManOperation( Dss_Man_t * p, int Type, int * pLits, int nLits, int * pPerm )
{
    Dss_Obj_t * pChildren[DAU_MAX_VAR];
    Dss_Obj_t * pObj, * pFanin, * pChild, * pMirror;
    int i, k, nChildren = 0, fCompl = 0, nSupp = 0;

    if ( Type == DAU_DSD_AND )
    {
        for ( k = 0; k < nLits; k++ )
        {
            pObj = Dss_Lit2Obj(p, pLits[k]);
            if ( Dss_IsComplement(pObj) || pObj->Type != DAU_DSD_AND )
                pChildren[nChildren++] = pObj;
            else
                Dss_ObjForEachChild( p, pObj, pChild, i )
                    pChildren[nChildren++] = pChild;
        }
        Dss_ObjSort( p, pChildren, nChildren );
    }
    else if ( Type == DAU_DSD_XOR )
    {
        for ( k = 0; k < nLits; k++ )
        {
            fCompl ^= Abc_LitIsCompl(pLits[k]);
            pObj = Dss_Lit2Obj(p, Abc_LitRegular(pLits[k]));
            if ( pObj->Type != DAU_DSD_XOR )
                pChildren[nChildren++] = pObj;
            else
                Dss_ObjForEachChild( p, pObj, pChild, i )
                {
                    assert( !Dss_IsComplement(pChild) );
                    pChildren[nChildren++] = pChild;
                }
        }
        Dss_ObjSort( p, pChildren, nChildren );
    }
    else if ( Type == DAU_DSD_MUX )
    {
        fCompl = Abc_LitIsCompl(pLits[1]) && Abc_LitIsCompl(pLits[2]);
        if ( Abc_LitIsCompl(pLits[0]) )
        {
            pChildren[nChildren++] = Dss_Lit2Obj(p, Abc_LitNotCond(pLits[0], 1));
            pChildren[nChildren++] = Dss_Lit2Obj(p, Abc_LitNotCond(pLits[2], fCompl));
            pChildren[nChildren++] = Dss_Lit2Obj(p, Abc_LitNotCond(pLits[1], fCompl));
        }
        else
        {
            pChildren[nChildren++] = Dss_Lit2Obj(p, Abc_LitNotCond(pLits[0], 0));
            pChildren[nChildren++] = Dss_Lit2Obj(p, Abc_LitNotCond(pLits[1], fCompl));
            pChildren[nChildren++] = Dss_Lit2Obj(p, Abc_LitNotCond(pLits[2], fCompl));
        }
    }
    else if ( Type == DAU_DSD_PRIME )
    {
        for ( k = 0; k < nLits; k++ )
             pChildren[nChildren++] = Dss_Lit2Obj(p, pLits[k]);
    }
    else assert( 0 );

    // shift subgraphs
    nSupp = 0;
    Vec_IntClear( p->vLeaves );
    for ( i = 0; i < nChildren; i++ )
    {
        pMirror = Dss_ManObj( p, Dss_Regular(pChildren[i])->Mirror );
        pFanin = Dss_ManShiftTree( p, pMirror, nSupp );
        assert( !Dss_IsComplement(pFanin) );
        assert( pFanin->nSupp > 0 );
        nSupp += pFanin->nSupp;
        Vec_IntPush( p->vLeaves, Abc_Var2Lit(pFanin->Id, Dss_IsComplement(pChildren[i])) );
    }
    // create new graph
    pObj = Dss_ObjFindOrAdd( p, Type, p->vLeaves );
    pObj->Mirror = pObj->Id;
    return Abc_Var2Lit( pObj->Id, fCompl );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dau_DsdTest()
{
    int nVars = 8;
//    char * pDsd = "[(ab)(cd)]";
    char * pDsd = "(!(a!(bh))[cde]!(fg))";
    Dss_Ntk_t * pNtk = Dss_NtkCreate( pDsd, nVars );
//    Dss_NtkPrint( pNtk );
//    Dss_NtkCheck( pNtk );
//    Dss_NtkTransform( pNtk );
//    Dss_NtkPrint( pNtk );
    Dss_NtkFree( pNtk );
    nVars = 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dau_DsdTest_()
{
    int nVars = 8;
    Vec_Vec_t * vFuncs = Vec_VecStart( nVars+1 );
    Vec_Int_t * vOne, * vTwo, * vThree;
    Dss_Man_t * p;
    int pEntries[3];
    int e0, e1, e2, iLit;
    int i, j, k, s;


    assert( nVars < DAU_MAX_VAR );
    p = Dss_ManAlloc( nVars );

    // init
    Vec_VecPushInt( vFuncs, 1, Dss_Obj2Lit(Dss_ManVar(p, 0)) );

    // enumerate
    for ( s = 2; s <= nVars; s++ )
    {
        for ( i = 1; i < s; i++ )
        for ( k = i; k < s; k++ )
        if ( i + k == s )
        {
            vOne = Vec_VecEntryInt( vFuncs, i );
            vTwo = Vec_VecEntryInt( vFuncs, k );
            Vec_IntForEachEntry( vOne, pEntries[0], e0 )
            Vec_IntForEachEntry( vTwo, pEntries[1], e1 )
            {
                iLit = Dss_ManOperation( p, DAU_DSD_AND, pEntries, 2, NULL );
                Vec_VecPushInt( vFuncs, s, iLit );

                pEntries[0] = Abc_LitNot( pEntries[0] );
                iLit = Dss_ManOperation( p, DAU_DSD_AND, pEntries, 2, NULL );
                Vec_VecPushInt( vFuncs, s, iLit );

                pEntries[1] = Abc_LitNot( pEntries[1] );
                iLit = Dss_ManOperation( p, DAU_DSD_AND, pEntries, 2, NULL );
                Vec_VecPushInt( vFuncs, s, iLit );

                pEntries[0] = Abc_LitNot( pEntries[0] );
                iLit = Dss_ManOperation( p, DAU_DSD_AND, pEntries, 2, NULL );
                Vec_VecPushInt( vFuncs, s, iLit );

                pEntries[1] = Abc_LitNot( pEntries[1] );
                iLit = Dss_ManOperation( p, DAU_DSD_XOR, pEntries, 2, NULL );
                Vec_VecPushInt( vFuncs, s, iLit );
            }
        }

        for ( i = 1; i < s; i++ )
        for ( k = i; k < s; k++ )
        for ( j = i; j < s; j++ )
        if ( i + k + j == s )
        {
            vOne = Vec_VecEntryInt( vFuncs, i );
            vTwo = Vec_VecEntryInt( vFuncs, k );
            vThree = Vec_VecEntryInt( vFuncs, j );
            Vec_IntForEachEntry( vOne, pEntries[0], e0 )
            Vec_IntForEachEntry( vTwo, pEntries[1], e1 )
            Vec_IntForEachEntry( vTwo, pEntries[2], e2 )
            {
                iLit = Dss_ManOperation( p, DAU_DSD_AND, pEntries, 3, NULL );
                Vec_VecPushInt( vFuncs, s, iLit );
            }
        }
    }

    Dss_ManFree( p );
    Vec_VecFree( vFuncs );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

