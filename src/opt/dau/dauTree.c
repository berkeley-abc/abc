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
#include "misc/util/utilTruth.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

typedef struct Dss_Fun_t_ Dss_Fun_t;
struct Dss_Fun_t_
{
    unsigned       iDsd  :    27;  // DSD literal
    unsigned       nFans :     5;  // fanin count
    unsigned char  pFans[0];       // fanins
};

typedef struct Dss_Ent_t_ Dss_Ent_t;
struct Dss_Ent_t_
{
    Dss_Fun_t *    pFunc;
    Dss_Ent_t *    pNext;
    unsigned       iDsd0  :   27;  // dsd entry
    unsigned       nWords :    5;  // total word count (struct + shared)
    unsigned       iDsd1  :   27;  // dsd entry
    unsigned       nShared:    5;  // shared count
    unsigned char  pShared[0];     // shared literals
};

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
    Vec_Int_t *    vCopies;        // temp
    word **        pTtElems;       // elementary TTs
};

static inline Dss_Obj_t *  Dss_Regular( Dss_Obj_t * p )                            { return (Dss_Obj_t *)((ABC_PTRUINT_T)(p) & ~01);                                    }
static inline Dss_Obj_t *  Dss_Not( Dss_Obj_t * p )                                { return (Dss_Obj_t *)((ABC_PTRUINT_T)(p) ^  01);                                    }
static inline Dss_Obj_t *  Dss_NotCond( Dss_Obj_t * p, int c )                     { return (Dss_Obj_t *)((ABC_PTRUINT_T)(p) ^ (c));                                    }
static inline int          Dss_IsComplement( Dss_Obj_t * p )                       { return (int)((ABC_PTRUINT_T)(p) & 01);                                             }

static inline void         Dss_ObjClean( Dss_Obj_t * pObj )                        { memset( pObj, 0, sizeof(Dss_Obj_t) );                                              }
static inline int          Dss_ObjId( Dss_Obj_t * pObj )                           { return pObj->Id;                                                                   }
static inline int          Dss_ObjType( Dss_Obj_t * pObj )                         { return pObj->Type;                                                                 }
static inline int          Dss_ObjSuppSize( Dss_Obj_t * pObj )                     { return pObj->nSupp;                                                                }
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
static inline int          Dss_ManLitSuppSize( Dss_Man_t * p, int iLit )           { return Dss_ManObj( p, Abc_Lit2Var(iLit) )->nSupp;                                  }

static inline int          Dss_Obj2Lit( Dss_Obj_t * pObj )                         { return Abc_Var2Lit(Dss_Regular(pObj)->Id, Dss_IsComplement(pObj));                 }
static inline Dss_Obj_t *  Dss_Lit2Obj( Dss_Man_t * p, int iLit )                  { return Dss_NotCond(Dss_ManObj(p, Abc_Lit2Var(iLit)), Abc_LitIsCompl(iLit));        }
static inline Dss_Obj_t *  Dss_ObjFanin( Dss_Man_t * p, Dss_Obj_t * pObj, int i )  { assert(i < (int)pObj->nFans); return Dss_ManObj(p, Abc_Lit2Var(pObj->pFans[i]));   }
static inline Dss_Obj_t *  Dss_ObjChild( Dss_Man_t * p, Dss_Obj_t * pObj, int i )  { assert(i < (int)pObj->nFans); return Dss_Lit2Obj(p, pObj->pFans[i]);               }

static inline int          Dss_EntWordNum( Dss_Ent_t * p )                         { return sizeof(Dss_Ent_t) / 8 + p->nShared / 4 + ((p->nShared & 3) > 0);            }
static inline int          Dss_FunWordNum( Dss_Fun_t * p )                         { assert(p->nFans >= 2); return (p->nFans + 4) / 8 + (((p->nFans + 4) & 7) > 0);     }
static inline word *       Dss_FunTruth( Dss_Fun_t * p )                           { assert(p->nFans >= 2); return (word *)p + Dss_FunWordNum(p);                       }


#define Dss_NtkForEachNode( p, pObj, i )                  \
    Vec_PtrForEachEntryStart( Dss_Obj_t *, p->vObjs, pObj, i, p->nVars + 1 )
#define Dss_ObjForEachFaninNtk( p, pObj, pFanin, i )      \
    for ( i = 0; (i < Dss_ObjFaninNum(pObj)) && ((pFanin) = Dss_ObjFaninNtk(p, pObj, i)); i++ )
#define Dss_ObjForEachChildNtk( p, pObj, pFanin, i )      \
    for ( i = 0; (i < Dss_ObjFaninNum(pObj)) && ((pFanin) = Dss_ObjChildNtk(p, pObj, i)); i++ )

#define Dss_ManForEachObj( p, pObj, i )                   \
    Vec_PtrForEachEntry( Dss_Obj_t *, p->vObjs, pObj, i )
#define Dss_ManForEachObjVec( vLits, p, pObj, i )         \
    for ( i = 0; (i < Vec_IntSize(vLits)) && ((pObj) = Dss_Lit2Obj(p, Vec_IntEntry(vLits,i))); i++ )
#define Dss_ObjForEachFanin( p, pObj, pFanin, i )         \
    for ( i = 0; (i < Dss_ObjFaninNum(pObj)) && ((pFanin) = Dss_ObjFanin(p, pObj, i)); i++ )
#define Dss_ObjForEachChild( p, pObj, pFanin, i )         \
    for ( i = 0; (i < Dss_ObjFaninNum(pObj)) && ((pFanin) = Dss_ObjChild(p, pObj, i)); i++ )

static inline int Dss_WordCountOnes( unsigned uWord )
{
    uWord = (uWord & 0x55555555) + ((uWord>>1) & 0x55555555);
    uWord = (uWord & 0x33333333) + ((uWord>>2) & 0x33333333);
    uWord = (uWord & 0x0F0F0F0F) + ((uWord>>4) & 0x0F0F0F0F);
    uWord = (uWord & 0x00FF00FF) + ((uWord>>8) & 0x00FF00FF);
    return  (uWord & 0x0000FFFF) + (uWord>>16);
}

static inline int Dss_Lit2Lit( int * pMapLit, int Lit )   { return Abc_Var2Lit( Abc_Lit2Var(pMapLit[Abc_Lit2Var(Lit)]), Abc_LitIsCompl(Lit) ^ Abc_LitIsCompl(pMapLit[Abc_Lit2Var(Lit)]) );   }


////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
 
/**Function*************************************************************

  Synopsis    [Elementary truth tables.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline word ** Dss_ManTtElems()
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
int Dss_NtkCollectPerm_rec( Dss_Ntk_t * p, Dss_Obj_t * pObj, int * pPermDsd, int * pnPerms )
{
    Dss_Obj_t * pChild;
    int k, fCompl = Dss_IsComplement(pObj);
    pObj = Dss_Regular( pObj );
    if ( pObj->Type == DAU_DSD_VAR )
    {
        pPermDsd[*pnPerms] = Abc_Var2Lit(pObj->iVar, fCompl);
        pObj->iVar = (*pnPerms)++;
        return fCompl;
    }
    Dss_ObjForEachChildNtk( p, pObj, pChild, k )
        if ( Dss_NtkCollectPerm_rec( p, pChild, pPermDsd, pnPerms ) )
            pObj->pFans[k] = (unsigned char)Abc_LitRegular((int)pObj->pFans[k]);
    return 0;
}
void Dss_NtkTransform( Dss_Ntk_t * p, int * pPermDsd )
{
    Dss_Obj_t * pChildren[DAU_MAX_VAR];
    Dss_Obj_t * pObj, * pChild;
    int i, k, nPerms;
    if ( Dss_Regular(p->pRoot)->Type == DAU_DSD_CONST0 )
        return;
    Dss_NtkForEachNode( p, pObj, i )
    {
        Dss_ObjForEachChildNtk( p, pObj, pChild, k )
            pChildren[k] = pChild;
        Dss_ObjSortNtk( p, pChildren, Dss_ObjFaninNum(pObj) );
        for ( k = 0; k < Dss_ObjFaninNum(pObj); k++ )
            pObj->pFans[k] = Dss_Obj2Lit( pChildren[k] );
    }
    nPerms = 0;
    if ( Dss_NtkCollectPerm_rec( p, p->pRoot, pPermDsd, &nPerms ) )
        p->pRoot = Dss_Regular(p->pRoot);
    assert( nPerms == (int)Dss_Regular(p->pRoot)->nSupp );
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
void Dss_ObjSort( Dss_Man_t * p, Dss_Obj_t ** pNodes, int nNodes, int * pPerm )
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
        if ( pPerm )
            ABC_SWAP( int, pPerm[i], pPerm[best_i] );
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
    // check structural canonicity
    assert( Type != DAU_DSD_MUX || Vec_IntSize(vFaninLits) == 3 );
    assert( Type != DAU_DSD_MUX || !Abc_LitIsCompl(Vec_IntEntry(vFaninLits, 0)) );
    assert( Type != DAU_DSD_MUX || !Abc_LitIsCompl(Vec_IntEntry(vFaninLits, 1)) || !Abc_LitIsCompl(Vec_IntEntry(vFaninLits, 2)) );
    // check that leaves are in good order
    if ( Type == DAU_DSD_AND || Type == DAU_DSD_XOR )
    Dss_ManForEachObjVec( vFaninLits, p, pFanin, i )
    {
        assert( Type != DAU_DSD_AND || Abc_LitIsCompl(Vec_IntEntry(vFaninLits, i)) || Dss_ObjType(pFanin) != DAU_DSD_AND );
        assert( Type != DAU_DSD_XOR || Dss_ObjType(pFanin) != DAU_DSD_XOR );
        assert( pPrev == NULL || Dss_ObjCompare(p, pPrev, pFanin) <= 0 );
        pPrev = pFanin;
    }
    // create new node
    pObj = Dss_ObjAlloc( p, Type, Vec_IntSize(vFaninLits), 0 );
    assert( pObj->nSupp == 0 );
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
    p->vCopies = Vec_IntAlloc( 32 );
    p->pTtElems = Dss_ManTtElems();
    return p;

}
void Dss_ManFree( Dss_Man_t * p )
{
    Vec_IntFreeP( &p->vCopies );
    Vec_IntFreeP( &p->vLeaves );
    Vec_PtrFreeP( &p->vObjs );
    Mem_FlexStop( p->pMem, 0 );
    ABC_FREE( p->pBins );
    ABC_FREE( p );
}
void Dss_ManPrint_rec( Dss_Man_t * p, Dss_Obj_t * pObj, int * pPermLits )
{
    char OpenType[7]  = {0, 0, 0, '(', '[', '<', '{'};
    char CloseType[7] = {0, 0, 0, ')', ']', '>', '}'};
    Dss_Obj_t * pFanin;
    int i;
    assert( !Dss_IsComplement(pObj) );
    if ( pObj->Type == DAU_DSD_CONST0 )
        { printf( "0" ); return; }
    if ( pObj->Type == DAU_DSD_VAR )
    {
        int iPermLit = pPermLits ? pPermLits[pObj->iVar] : Abc_Var2Lit(pObj->iVar, 0);
        printf( "%s%c", Abc_LitIsCompl(iPermLit)? "!":"", 'a' + Abc_Lit2Var(iPermLit) );
        return;
    }
    printf( "%c", OpenType[pObj->Type] );
    Dss_ObjForEachFanin( p, pObj, pFanin, i )
    {
        printf( "%s", Dss_ObjFaninC(pObj, i) ? "!":"" );
        Dss_ManPrint_rec( p, pFanin, pPermLits );
    }
    printf( "%c", CloseType[pObj->Type] );
}
void Dss_ManPrintOne( Dss_Man_t * p, int iDsdLit, int * pPermLits )
{
    printf( "%6d : ", Abc_Lit2Var(iDsdLit) );
    printf( "%2d ",   Dss_ManLitSuppSize(p, iDsdLit) );
    printf( "%s",     Abc_LitIsCompl(iDsdLit) ? "!" : ""  );
    Dss_ManPrint_rec( p, Dss_ManObj(p, Abc_Lit2Var(iDsdLit)), pPermLits );
    printf( "\n" );
}
void Dss_ManPrintAll( Dss_Man_t * p )
{
    Dss_Obj_t * pObj;
    int i, nSuppMax = 0;
    printf( "DSD manager contains %d objects:\n", Vec_PtrSize(p->vObjs) );
    Dss_ManForEachObj( p, pObj, i )
    {
        if ( (int)pObj->nSupp < nSuppMax )
            continue;
        Dss_ManPrintOne( p, Dss_Obj2Lit(pObj), NULL );
        nSuppMax = Abc_MaxInt( nSuppMax, pObj->nSupp );
    }
    printf( "\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dss_NtkRebuild( Dss_Man_t * p, Dss_Ntk_t * pNtk )
{
    Dss_Obj_t * pObj, * pFanin, * pObjNew;
    int i, k;
    assert( p->nVars == pNtk->nVars );
    if ( Dss_Regular(pNtk->pRoot)->Type == DAU_DSD_CONST0 )
        return Dss_IsComplement(pNtk->pRoot);
    if ( Dss_Regular(pNtk->pRoot)->Type == DAU_DSD_VAR )
        return Abc_Var2Lit( Dss_Regular(pNtk->pRoot)->iVar, Dss_IsComplement(pNtk->pRoot) );
    Vec_IntFill( p->vCopies, Vec_PtrSize(pNtk->vObjs), -1 );
    Dss_NtkForEachNode( pNtk, pObj, i )
    {
        Vec_IntClear( p->vLeaves );
        Dss_ObjForEachFaninNtk( pNtk, pObj, pFanin, k )
            if ( pFanin->Type == DAU_DSD_VAR )
                Vec_IntPush( p->vLeaves, Abc_Var2Lit(pFanin->iVar+1, 0) );
            else
                Vec_IntPush( p->vLeaves, Abc_Lit2Lit(Vec_IntArray(p->vCopies), pObj->pFans[k]) );
        pObjNew = Dss_ObjCreate( p, pObj->Type, p->vLeaves );
        Vec_IntWriteEntry( p->vCopies, Dss_ObjId(pObj), Dss_ObjId(pObjNew) );
    }
    return Abc_Lit2Lit( Vec_IntArray(p->vCopies), Dss_Obj2Lit(pNtk->pRoot) );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dss_ManComputeTruth_rec( Dss_Man_t * p, Dss_Obj_t * pObj, int nVars, word * pRes, int * pPermLits )
{
    Dss_Obj_t * pChild;
    int nWords = Abc_TtWordNum(nVars);
    int i, fCompl = Dss_IsComplement(pObj);
    pObj = Dss_Regular(pObj);
    if ( pObj->Type == DAU_DSD_VAR )
    {
        int iPermLit = pPermLits[(int)pObj->iVar];
        assert( (int)pObj->iVar < nVars );
        Abc_TtCopy( pRes, p->pTtElems[Abc_Lit2Var(iPermLit)], nWords, fCompl ^ Abc_LitIsCompl(iPermLit) );
        return;
    }
    if ( pObj->Type == DAU_DSD_AND || pObj->Type == DAU_DSD_XOR )
    {
        word pTtTemp[DAU_MAX_WORD];
        if ( pObj->Type == DAU_DSD_AND )
            Abc_TtConst1( pRes, nWords );
        else
            Abc_TtConst0( pRes, nWords );
        Dss_ObjForEachChild( p, pObj, pChild, i )
        {
            Dss_ManComputeTruth_rec( p, pChild, nVars, pTtTemp, pPermLits );
            if ( pObj->Type == DAU_DSD_AND )
                Abc_TtAnd( pRes, pRes, pTtTemp, nWords, 0 );
            else
                Abc_TtXor( pRes, pRes, pTtTemp, nWords, 0 );
        }
        if ( fCompl ) Abc_TtNot( pRes, nWords );
        return;
    }
    if ( pObj->Type == DAU_DSD_MUX ) // mux
    {
        word pTtTemp[3][DAU_MAX_WORD];
        Dss_ObjForEachChild( p, pObj, pChild, i )
            Dss_ManComputeTruth_rec( p, pChild, nVars, pTtTemp[i], pPermLits );
        assert( i == 3 );
        Abc_TtMux( pRes, pTtTemp[0], pTtTemp[1], pTtTemp[2], nWords );
        if ( fCompl ) Abc_TtNot( pRes, nWords );
        return;
    }
    if ( pObj->Type == DAU_DSD_PRIME ) // function
    {
    }
    assert( 0 );

}
word * Dss_ManComputeTruth( Dss_Man_t * p, int iDsd, int nVars, int * pPermLits )
{
    int nWords = Abc_TtWordNum( nVars );
    word * pRes = p->pTtElems[DAU_MAX_VAR];
    assert( nVars <= DAU_MAX_VAR );
    if ( iDsd == 0 )
        Abc_TtConst0( pRes, nWords );
    else if ( iDsd == 1 )
        Abc_TtConst1( pRes, nWords );
    else if ( Abc_Lit2Var(iDsd) < p->nVars )
    {
        int iPermLit = pPermLits[Abc_Lit2Var(iDsd)];
        Abc_TtCopy( pRes, p->pTtElems[Abc_Lit2Var(iPermLit)], nWords, Abc_LitIsCompl(iDsd) ^ Abc_LitIsCompl(iPermLit) );
    }
    else
        Dss_ManComputeTruth_rec( p, Dss_Lit2Obj(p, iDsd), nVars, pRes, pPermLits );
    return pRes;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dss_Obj_t * Dss_ManShiftTree_rec( Dss_Man_t * p, Dss_Obj_t * pObj, int Shift )
{
    Vec_Int_t * vFaninLits;
    Dss_Obj_t * pMirror, * pFanin, * pObjNew;
    int i, nSupp = Shift;
    assert( !Dss_IsComplement(pObj) );
    assert( pObj->Mirror == pObj->Id );
    if ( Shift == 0 )
        return pObj;
    if ( pObj->Type == DAU_DSD_VAR )
    {
        assert( (int)pObj->iVar + Shift < p->nVars );
        return Dss_ManVar( p, pObj->iVar + Shift );
    }
    // collect fanins
    vFaninLits = Vec_IntAlloc( 10 );
    Dss_ObjForEachFanin( p, pObj, pFanin, i )
    {
        pMirror = Dss_ManObj( p, pFanin->Mirror );
        pFanin = Dss_ManShiftTree_rec( p, pMirror, nSupp );
        Vec_IntPush( vFaninLits, Abc_Var2Lit(pFanin->Id, Dss_ObjFaninC(pObj, i)) );
        assert( pFanin->nSupp > 0 );
        nSupp += pFanin->nSupp;
    }
    // create new graph
    pObjNew = Dss_ObjFindOrAdd( p, pObj->Type, vFaninLits );
    pObjNew->Mirror = pObj->Id;
    Vec_IntFree( vFaninLits );
    return pObjNew;
}
void Dss_ManShiftTree( Dss_Man_t * p, Dss_Obj_t ** pChildren, int nChildren, Vec_Int_t * vLeaves )
{
    int i, nSupp = 0;
    Vec_IntClear( vLeaves );
    for ( i = 0; i < nChildren; i++ )
    {
        Dss_Obj_t * pMirror = Dss_ManObj( p, Dss_Regular(pChildren[i])->Mirror );
        Dss_Obj_t * pFanin = Dss_ManShiftTree_rec( p, pMirror, nSupp );
        assert( !Dss_IsComplement(pFanin) );
        Vec_IntPush( vLeaves, Abc_Var2Lit(pFanin->Id, Dss_IsComplement(pChildren[i])) );
        assert( pFanin->nSupp > 0 );
        nSupp += pFanin->nSupp;
    }
}

/**Function*************************************************************

  Synopsis    [Performs DSD operation on the two literals.]

  Description [Returns the perm of the resulting literals. The perm size 
  is equal to the number of support variables. The perm variables are 0-based
  numbers of pLits[0] followed by nLits[0]-based numbers of pLits[1].]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dss_ManOperation( Dss_Man_t * p, int Type, int * pLits, int nLits, unsigned char * pPerm )
{
    Dss_Obj_t * pChildren[DAU_MAX_VAR];
    Dss_Obj_t * pObj, * pChild;
    int i, k, nChildren = 0, fCompl = 0;

    assert( Type == DAU_DSD_AND || pPerm == NULL );
    if ( Type == DAU_DSD_AND && pPerm != NULL )
    {
        int pBegEnd[DAU_MAX_VAR];
        int j, nSSize = 0;
        for ( k = 0; k < nLits; k++ )
        {
            pObj = Dss_Lit2Obj(p, pLits[k]);
            if ( Dss_IsComplement(pObj) || pObj->Type != DAU_DSD_AND )
            {
                pBegEnd[nChildren] = (nSSize << 16) | (nSSize + Dss_Regular(pObj)->nSupp);
                nSSize += Dss_Regular(pObj)->nSupp;
                pChildren[nChildren++] = pObj;
            }
            else
                Dss_ObjForEachChild( p, pObj, pChild, i )
                {
                    pBegEnd[nChildren] = (nSSize << 16) | (nSSize + Dss_Regular(pChild)->nSupp);
                    nSSize += Dss_Regular(pChild)->nSupp;
                    pChildren[nChildren++] = pChild;
                }
        }
        Dss_ObjSort( p, pChildren, nChildren, pBegEnd );
        // create permutation
        for ( j = i = 0; i < nChildren; i++ )
            for ( k = (pBegEnd[i] >> 16); k < (pBegEnd[i] & 0xFF); k++ )
                pPerm[j++] = (unsigned char)Abc_Var2Lit( k, 0 );
        assert( j == nSSize );
    }
    else if ( Type == DAU_DSD_AND )
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
        Dss_ObjSort( p, pChildren, nChildren, NULL );
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
        Dss_ObjSort( p, pChildren, nChildren, NULL );
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
    Dss_ManShiftTree( p, pChildren, nChildren, p->vLeaves );
    // create new graph
    pObj = Dss_ObjFindOrAdd( p, Type, p->vLeaves );
    pObj->Mirror = pObj->Id;
    return Abc_Var2Lit( pObj->Id, fCompl );
}
Dss_Fun_t * Dss_ManOperationFun( Dss_Man_t * p, int * iDsd, int * nFans )
{
    static char Buffer[100];
    Dss_Fun_t * pFun = (Dss_Fun_t *)Buffer;
    pFun->iDsd = Dss_ManOperation( p, DAU_DSD_AND, iDsd, 2, pFun->pFans );
    pFun->nFans = nFans[0] + nFans[1];
    assert( (int)pFun->nFans == Dss_ManLitSuppSize(p, pFun->iDsd) );
    return pFun;
}

/**Function*************************************************************

  Synopsis    [Performs AND on two DSD functions with support overlap.]

  Description [Returns the perm of the resulting literals. The perm size 
  is equal to the number of support variables. The perm variables are 0-based
  numbers of pLits[0] followed by nLits[0]-based numbers of pLits[1].]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Dss_Fun_t * Dss_ManBooleanAnd( Dss_Man_t * p, Dss_Ent_t * pEnt, int * nFans )
{
    static char Buffer[100];
    Dss_Fun_t * pFun = (Dss_Fun_t *)Buffer;
    Dss_Ntk_t * pNtk;
    word * pTruthOne, pTruth[DAU_MAX_WORD];
    char pDsd[DAU_MAX_STR];
    int pMapDsd2Truth[DAU_MAX_VAR];
    int pPermLits[DAU_MAX_VAR];
    int pPermDsd[DAU_MAX_VAR];
    int i, nNonDec, nSuppSize = 0;
    // create first truth table
    for ( i = 0; i < nFans[0]; i++ )
    {
        pMapDsd2Truth[nSuppSize] = i;
        pPermLits[i] = Abc_Var2Lit( nSuppSize++, 0 );
    }
    pTruthOne = Dss_ManComputeTruth( p, pEnt->iDsd0, p->nVars, pPermLits );
    Abc_TtCopy( pTruth, pTruthOne, Abc_TtWordNum(p->nVars), 0 );
//Kit_DsdPrintFromTruth( pTruthOne, p->nVars );  printf( "\n" );
    // create second truth table
    for ( i = 0; i < nFans[1]; i++ )
        pPermLits[i] = -1;
    for ( i = 0; i < (int)pEnt->nShared; i++ )
        pPermLits[pEnt->pShared[2*i+0]] = pEnt->pShared[2*i+1];
    for ( i = 0; i < nFans[1]; i++ )
        if ( pPermLits[i] == -1 )
        {
            pMapDsd2Truth[nSuppSize] = nFans[0] + i;
            pPermLits[i] = Abc_Var2Lit( nSuppSize++, 0 );
        }
    pTruthOne = Dss_ManComputeTruth( p, pEnt->iDsd1, p->nVars, pPermLits );
//Kit_DsdPrintFromTruth( pTruthOne, p->nVars );  printf( "\n" );
    Abc_TtAnd( pTruth, pTruth, pTruthOne, Abc_TtWordNum(p->nVars), 0 );
    // perform decomposition
    nNonDec = Dau_DsdDecompose( pTruth, nSuppSize, 0, pDsd );
    // derive network and convert it into the manager
    pNtk = Dss_NtkCreate( pDsd, p->nVars );
Dss_NtkPrint( pNtk );    
    Dss_NtkCheck( pNtk );
    Dss_NtkTransform( pNtk, pPermDsd );
Dss_NtkPrint( pNtk );    
    pFun->iDsd = Dss_NtkRebuild( p, pNtk );
    Dss_NtkFree( pNtk );
    // pPermDsd maps vars of iDsdRes into literals of pTruth
    // translate this map into the one that maps vars of iDsdRes into literals of cut
    pFun->nFans = Dss_ManLitSuppSize( p, pFun->iDsd );
    for ( i = 0; i < (int)pFun->nFans; i++ )
        pFun->pFans[i] = (unsigned char)Abc_Lit2Lit( pMapDsd2Truth, pPermDsd[i] );
    return pFun;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
// returns mapping of variables of dsd1 into literals of dsd0
Dss_Ent_t * Dss_ManSharedMap( Dss_Man_t * p, int * iDsd, int * nFans, int ** pFans, unsigned uSharedMask )
{
    static char Buffer[100];
    Dss_Ent_t * pEnt = (Dss_Ent_t *)Buffer;
    pEnt->iDsd0 = iDsd[0];
    pEnt->iDsd1 = iDsd[1];
    pEnt->nShared = 0;
    if ( uSharedMask )
    {
        int i, g, pMapGtoL[DAU_MAX_VAR] = {-1};
        for ( i = 0; i < nFans[0]; i++ )
            pMapGtoL[ Abc_Lit2Var(pFans[0][i]) ] = Abc_Var2Lit( i, Abc_LitIsCompl(pFans[0][i]) );
        for ( i = 0; i < nFans[1]; i++ )
        {
            g = Abc_Lit2Var( pFans[1][i] );
            if ( (uSharedMask >> g) & 1 )
            {
                assert( pMapGtoL[g] >= 0 );
                pEnt->pShared[2*pEnt->nShared+0] = (unsigned char)i;
                pEnt->pShared[2*pEnt->nShared+1] = (unsigned char)Abc_LitNotCond( pMapGtoL[g], Abc_LitIsCompl(pFans[1][i]) );
                pEnt->nShared++;
            }
        }
    }
    pEnt->nWords = Dss_EntWordNum( pEnt );
    return pEnt;
}
// merge two DSD functions
int Dss_ManMerge( Dss_Man_t * p, int * iDsd, int * nFans, int ** pFans, unsigned uSharedMask, int nKLutSize, unsigned char * pPermRes )
{
    Dss_Ent_t * pEnt;
    Dss_Fun_t * pFun;
    int i;
    assert( iDsd[0] <= iDsd[1] );
    // constant argument
    if ( iDsd[0] == 0 ) return 0;
    if ( iDsd[0] == 1 ) return iDsd[1];
    if ( iDsd[1] == 0 ) return 0;
    if ( iDsd[1] == 1 ) return iDsd[0];
    // no overlap
    assert( nFans[0] == Dss_ManLitSuppSize(p, iDsd[0]) );
    assert( nFans[1] == Dss_ManLitSuppSize(p, iDsd[1]) );
    assert( nFans[0] + nFans[1] <= nKLutSize + Dss_WordCountOnes(uSharedMask) );
    // create map of shared variables
    pEnt = Dss_ManSharedMap( p, iDsd, nFans, pFans, uSharedMask );
    // check cache
    if ( uSharedMask == 0 )
        pFun = Dss_ManOperationFun( p, iDsd, nFans );
    else
        pFun = Dss_ManBooleanAnd( p, pEnt, nFans );
    assert( (int)pFun->nFans == Dss_ManLitSuppSize(p, pFun->iDsd) );
    assert( (int)pFun->nFans <= nKLutSize );
    // create permutation
    for ( i = 0; i < (int)pFun->nFans; i++ )
        printf( "%d ", pFun->pFans[i] );
    printf( "\n" );

    for ( i = 0; i < (int)pFun->nFans; i++ )
        if ( pFun->pFans[i] < 2 * nFans[0] ) // first dec
            pPermRes[i] = (unsigned char)Dss_Lit2Lit( pFans[0], pFun->pFans[i] );
        else
            pPermRes[i] = (unsigned char)Dss_Lit2Lit( pFans[1], pFun->pFans[i] - 2 * nFans[0] );

    // create permutation
    for ( i = 0; i < (int)pFun->nFans; i++ )
        printf( "%d ", pPermRes[i] );
    printf( "\n" );

    return pFun->iDsd;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dss_ObjCheckTransparent( Dss_Man_t * p, Dss_Obj_t * pObj )
{
    Dss_Obj_t * pFanin;
    int i;
    if ( pObj->Type == DAU_DSD_VAR )
        return 1;
    if ( pObj->Type == DAU_DSD_AND )
        return 0;
    if ( pObj->Type == DAU_DSD_XOR )
    {
        Dss_ObjForEachFanin( p, pObj, pFanin, i )
            if ( Dss_ObjCheckTransparent( p, pFanin ) )
                return 1;
        return 0;
    }
    if ( pObj->Type == DAU_DSD_MUX )
    {
        pFanin = Dss_ObjFanin( p, pObj, 1 );
        if ( !Dss_ObjCheckTransparent(p, pFanin) )
            return 0;
        pFanin = Dss_ObjFanin( p, pObj, 2 );
        if ( !Dss_ObjCheckTransparent(p, pFanin) )
            return 0;
        return 1;
    }
    assert( pObj->Type == DAU_DSD_PRIME );
    return 0;
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
    int nVars = 6;
    Vec_Vec_t * vFuncs = Vec_VecStart( nVars+1 );
    Vec_Int_t * vOne, * vTwo, * vThree, * vRes;
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
        vRes = Vec_VecEntryInt( vFuncs, s );
        for ( i = 1; i < s; i++ )
        for ( k = i; k < s; k++ )
        if ( i + k == s )
        {
            vOne = Vec_VecEntryInt( vFuncs, i );
            vTwo = Vec_VecEntryInt( vFuncs, k );
            Vec_IntForEachEntry( vOne, pEntries[0], e0 )
            Vec_IntForEachEntry( vTwo, pEntries[1], e1 )
            {
                int fAddInv0 = !Dss_ObjCheckTransparent( p, Dss_ManObj(p, Abc_Lit2Var(pEntries[0])) );
                int fAddInv1 = !Dss_ObjCheckTransparent( p, Dss_ManObj(p, Abc_Lit2Var(pEntries[1])) );

                iLit = Dss_ManOperation( p, DAU_DSD_AND, pEntries, 2, NULL );
                assert( !Abc_LitIsCompl(iLit) );
                Vec_IntPush( vRes, iLit );

                if ( fAddInv0 )
                {
                    pEntries[0] = Abc_LitNot( pEntries[0] );
                    iLit = Dss_ManOperation( p, DAU_DSD_AND, pEntries, 2, NULL );
                    pEntries[0] = Abc_LitNot( pEntries[0] );
                    assert( !Abc_LitIsCompl(iLit) );
                    Vec_IntPush( vRes, iLit );
                }

                if ( fAddInv1 )
                {
                    pEntries[1] = Abc_LitNot( pEntries[1] );
                    iLit = Dss_ManOperation( p, DAU_DSD_AND, pEntries, 2, NULL );
                    pEntries[1] = Abc_LitNot( pEntries[1] );
                    assert( !Abc_LitIsCompl(iLit) );
                    Vec_IntPush( vRes, iLit );
                }

                if ( fAddInv0 && fAddInv1 )
                {
                    pEntries[0] = Abc_LitNot( pEntries[0] );
                    pEntries[1] = Abc_LitNot( pEntries[1] );
                    iLit = Dss_ManOperation( p, DAU_DSD_AND, pEntries, 2, NULL );
                    pEntries[0] = Abc_LitNot( pEntries[0] );
                    pEntries[1] = Abc_LitNot( pEntries[1] );
                    assert( !Abc_LitIsCompl(iLit) );
                    Vec_IntPush( vRes, iLit );
                }

                iLit = Dss_ManOperation( p, DAU_DSD_XOR, pEntries, 2, NULL );
                assert( !Abc_LitIsCompl(iLit) );
                Vec_IntPush( vRes, iLit );
            }
        }

        for ( i = 1; i < s; i++ )
        for ( k = 1; k < s; k++ )
        for ( j = 1; j < s; j++ )
        if ( i + k + j == s )
        {
            vOne   = Vec_VecEntryInt( vFuncs, i );
            vTwo   = Vec_VecEntryInt( vFuncs, k );
            vThree = Vec_VecEntryInt( vFuncs, j );
            Vec_IntForEachEntry( vOne,   pEntries[0], e0 )
            Vec_IntForEachEntry( vTwo,   pEntries[1], e1 )
            Vec_IntForEachEntry( vThree, pEntries[2], e2 )
            {
                int fAddInv0 = !Dss_ObjCheckTransparent( p, Dss_ManObj(p, Abc_Lit2Var(pEntries[0])) );
                int fAddInv1 = !Dss_ObjCheckTransparent( p, Dss_ManObj(p, Abc_Lit2Var(pEntries[1])) );
                int fAddInv2 = !Dss_ObjCheckTransparent( p, Dss_ManObj(p, Abc_Lit2Var(pEntries[2])) );

                if ( !fAddInv0 && k > j )
                    continue;

                iLit = Dss_ManOperation( p, DAU_DSD_MUX, pEntries, 3, NULL );
                assert( !Abc_LitIsCompl(iLit) );
                Vec_IntPush( vRes, iLit );

                if ( fAddInv1 )
                {
                    pEntries[1] = Abc_LitNot( pEntries[1] );
                    iLit = Dss_ManOperation( p, DAU_DSD_MUX, pEntries, 3, NULL );
                    pEntries[1] = Abc_LitNot( pEntries[1] );
                    assert( !Abc_LitIsCompl(iLit) );
                    Vec_IntPush( vRes, iLit );
                }

                if ( fAddInv2 )
                {
                    pEntries[2] = Abc_LitNot( pEntries[2] );
                    iLit = Dss_ManOperation( p, DAU_DSD_MUX, pEntries, 3, NULL );
                    pEntries[2] = Abc_LitNot( pEntries[2] );
                    assert( !Abc_LitIsCompl(iLit) );
                    Vec_IntPush( vRes, iLit );
                }
            }
        }
        Vec_IntUniqify( vRes );
    }
    Dss_ManPrintAll( p );

    Dss_ManFree( p );
    Vec_VecFree( vFuncs );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dau_DsdTest444()
{
    Dss_Man_t * p = Dss_ManAlloc( 6 );
    int iLit1[3] = { 2, 4 };
    int iLit2[3] = { 2, 4, 6 };
    int iRes[5];
    int nFans[2] = { 4, 3 };
    int pPermLits1[4] = { 0, 2, 5, 6 };
    int pPermLits2[5] = { 2, 9, 10 };
    int * pPermLits[2] = { pPermLits1, pPermLits2 };
    unsigned char pPermRes[6];
    int pPermResInt[6];
    unsigned uMaskShared = 2;
    int i;

    iRes[0] = 1 ^ Dss_ManOperation( p, DAU_DSD_AND, iLit1, 2, NULL );
    iRes[1] = iRes[0]; 
    iRes[2] = 1 ^ Dss_ManOperation( p, DAU_DSD_AND, iRes, 2, NULL );
    iRes[3] = Dss_ManOperation( p, DAU_DSD_AND, iLit2, 3, NULL );

    Dss_ManPrintOne( p, iRes[0], NULL );
    Dss_ManPrintOne( p, iRes[2], NULL );
    Dss_ManPrintOne( p, iRes[3], NULL );

    Dss_ManPrintOne( p, iRes[2], pPermLits1 );
    Dss_ManPrintOne( p, iRes[3], pPermLits2 );

    iRes[4] = Dss_ManMerge( p, iRes+2, nFans, pPermLits, uMaskShared, 6, pPermRes );

    for ( i = 0; i < 6; i++ )
        pPermResInt[i] = pPermRes[i];

    Dss_ManPrintOne( p, iRes[4], NULL );
    Dss_ManPrintOne( p, iRes[4], pPermResInt );

    Dss_ManFree( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

