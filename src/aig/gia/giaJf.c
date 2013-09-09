/**CFile****************************************************************

  FileName    [giaJf.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaJf.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"
#include "misc/vec/vecSet.h"
#include "misc/extra/extra.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define JF_LEAF_MAX   6
#define JF_CUT_MAX   16
#define JF_EDGE_LIM  10

typedef struct Jf_Cut_t_ Jf_Cut_t; 
struct Jf_Cut_t_
{
    unsigned         Sign;   
    float            Flow;
    int              Time;
    int              iFunc;
    int              Cost;
    int              pCut[JF_LEAF_MAX+2];
};

typedef struct Jf_Man_t_ Jf_Man_t; 
struct Jf_Man_t_
{
    Gia_Man_t *      pGia;        // user's manager
    Jf_Par_t *       pPars;       // users parameter
    Sdm_Man_t *      pDsd;        // extern DSD manager
    Vec_Int_t        vCuts;       // cuts for each node
    Vec_Int_t        vArr;        // arrival time
    Vec_Int_t        vDep;        // departure time
    Vec_Flt_t        vFlow;       // area flow
    Vec_Flt_t        vRefs;       // ref counters
    Vec_Set_t        pMem;        // cut storage
    Vec_Int_t *      vTemp;       // temporary
    float (*pCutCmp) (Jf_Cut_t *, Jf_Cut_t *);// procedure to compare cuts
    abctime          clkStart;    // starting time
    word             CutCount[4]; // statistics
    int              nCoarse;     // coarse nodes
};

static inline int    Jf_ObjCutH( Jf_Man_t * p, int i )    { return Vec_IntEntry(&p->vCuts, i);                       }
static inline int *  Jf_ObjCuts( Jf_Man_t * p, int i )    { return (int *)Vec_SetEntry(&p->pMem, Jf_ObjCutH(p, i));  }
static inline int *  Jf_ObjCutBest( Jf_Man_t * p, int i ) { return Jf_ObjCuts(p, i) + 1;                             }
static inline int    Jf_ObjArr( Jf_Man_t * p, int i )     { return Vec_IntEntry(&p->vArr, i);                        }
static inline int    Jf_ObjDep( Jf_Man_t * p, int i )     { return Vec_IntEntry(&p->vDep, i);                        }
static inline float  Jf_ObjFlow( Jf_Man_t * p, int i )    { return Vec_FltEntry(&p->vFlow, i);                       }
static inline float  Jf_ObjRefs( Jf_Man_t * p, int i )    { return Vec_FltEntry(&p->vRefs, i);                       }
//static inline int    Jf_ObjLit( int i )                   { return i;                                                }
static inline int    Jf_ObjLit( int i )                   { return Abc_Var2Lit( i, 0 );                              }

static inline int    Jf_CutSize( int * pCut )             { return pCut[0] & 0x1F;                                   }
static inline int    Jf_CutFunc( int * pCut )             { return (pCut[0] >> 5) & 0x7FF;                           }
static inline int    Jf_CutCost( int * pCut )             { return (pCut[0] >> 16) & 0xFFFF;                         }
static inline int *  Jf_CutLits( int * pCut )             { return pCut + 1;                                         }
static inline int    Jf_CutLit( int * pCut, int i )       { assert(i);return pCut[i];                                }
//static inline int    Jf_CutVar( int * pCut, int i )       { assert(i); return pCut[i];                               }
static inline int    Jf_CutVar( int * pCut, int i )       {  assert(i);return Abc_Lit2Var(pCut[i]);                  }

#define Jf_ObjForEachCut( pList, pCut, i )   for ( i = 0, pCut = pList + 1; i < pList[0]; i++, pCut += Jf_CutSize(pCut) + 1 )
#define Jf_CutForEachVar( pCut, Var, i )     for ( i = 1; i <= Jf_CutSize(pCut) && (Var = Jf_CutVar(pCut, i)); i++ )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computing references while discounting XOR/MUX.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float * Jf_ManInitRefs( Jf_Man_t * pMan )
{
    Gia_Man_t * p = pMan->pGia;
    Gia_Obj_t * pObj, * pCtrl, * pData0, * pData1;
    float * pRes; int i;
    assert( p->pRefs == NULL );
    p->pRefs = ABC_CALLOC( int, Gia_ManObjNum(p) );
    Gia_ManForEachAnd( p, pObj, i )
    {
        Gia_ObjRefFanin0Inc( p, pObj );
        if ( Gia_ObjIsBuf(pObj) )
            continue;
        Gia_ObjRefFanin1Inc( p, pObj );
        if ( !Gia_ObjIsMuxType(pObj) )
            continue;
        // discount XOR/MUX
        pCtrl = Gia_ObjRecognizeMux( pObj, &pData1, &pData0 );
        Gia_ObjRefDec( p, Gia_Regular(pCtrl) );
        if ( Gia_Regular(pData1) == Gia_Regular(pData0) )
            Gia_ObjRefDec( p, Gia_Regular(pData1) );
    }
    Gia_ManForEachCo( p, pObj, i )
        Gia_ObjRefFanin0Inc( p, pObj );
    // mark XOR/MUX internal nodes, which are not used elsewhere
    if ( pMan->pPars->fCoarsen )
    {
        pMan->nCoarse = 0;
        Gia_ManForEachAnd( p, pObj, i )
        {
            if ( Gia_ObjIsBuf(pObj) || !Gia_ObjIsMuxType(pObj) )
                continue;
            if ( Gia_ObjRefNum(p, Gia_ObjFanin0(pObj)) == 1 )
                Gia_ObjFanin0(pObj)->fMark0 = 1, pMan->nCoarse++;
            if ( Gia_ObjRefNum(p, Gia_ObjFanin1(pObj)) == 1 )
                Gia_ObjFanin1(pObj)->fMark0 = 1, pMan->nCoarse++;
        }
    }
    // multiply by factor
    pRes = ABC_ALLOC( float, Gia_ManObjNum(p) );
    for ( i = 0; i < Gia_ManObjNum(p); i++ )
        pRes[i] = Abc_MaxInt( 1, p->pRefs[i] );
    return pRes;
}

/**Function*************************************************************

  Synopsis    [Manager manipulation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Jf_Man_t * Jf_ManAlloc( Gia_Man_t * pGia, Jf_Par_t * pPars )
{
    Jf_Man_t * p;
    assert( pPars->nLutSize <= JF_LEAF_MAX );
    assert( pPars->nCutNum <= JF_CUT_MAX );
    Vec_IntFreeP( &pGia->vMapping );
    p = ABC_CALLOC( Jf_Man_t, 1 );
    p->pGia      = pGia;
    p->pPars     = pPars;
    p->pDsd      = pPars->fCutMin ? Sdm_ManRead() : NULL;
    Vec_IntFill( &p->vCuts, Gia_ManObjNum(pGia), 0 );
    Vec_IntFill( &p->vArr,  Gia_ManObjNum(pGia), 0 );
    Vec_IntFill( &p->vDep,  Gia_ManObjNum(pGia), 0 );
    Vec_FltFill( &p->vFlow, Gia_ManObjNum(pGia), 0 );
    p->vRefs.nCap = p->vRefs.nSize = Gia_ManObjNum(pGia);
    p->vRefs.pArray = Jf_ManInitRefs( p );
    Vec_SetAlloc_( &p->pMem, 20 );
    p->vTemp     = Vec_IntAlloc( 1000 );
    p->clkStart  = Abc_Clock();
    return p;
}
void Jf_ManFree( Jf_Man_t * p )
{
    if ( p->pPars->fVerbose && p->pDsd )
        Sdm_ManPrintDsdStats( p->pDsd, p->pPars->fVeryVerbose );
    if ( p->pPars->fCoarsen )
        Gia_ManCleanMark0( p->pGia );
    ABC_FREE( p->pGia->pRefs );
    ABC_FREE( p->vCuts.pArray );
    ABC_FREE( p->vArr.pArray );
    ABC_FREE( p->vDep.pArray );
    ABC_FREE( p->vFlow.pArray );
    ABC_FREE( p->vRefs.pArray );
    Vec_SetFree_( &p->pMem );
    Vec_IntFreeP( &p->vTemp );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Cut functions.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Jf_CutPrint( int * pCut )
{
    int i; 
    printf( "%d {", Jf_CutSize(pCut) );
    for ( i = 1; i <= Jf_CutSize(pCut); i++ )
        printf( " %d", Jf_CutLit(pCut, i) );
    printf( " }\n" );
}
static inline void Jf_ObjCutPrint( int * pCuts )
{
    int i, * pCut; 
    Jf_ObjForEachCut( pCuts, pCut, i )
        Jf_CutPrint( pCut );
    printf( "\n" );
}
static inline void Jf_ObjBestCutConePrint( Jf_Man_t * p, Gia_Obj_t * pObj )
{
    int * pCut = Jf_ObjCutBest( p, Gia_ObjId(p->pGia, pObj) );
    printf( "Best cut of node %d : ", Gia_ObjId(p->pGia, pObj) );
    Jf_CutPrint( pCut );
    Gia_ManPrintCone( p->pGia, pObj, Jf_CutLits(pCut), Jf_CutSize(pCut), p->vTemp );
}
static inline void Jf_CutCheck( int * pCut )
{
    int i, k;
    for ( i = 2; i <= Jf_CutSize(pCut); i++ )
        for ( k = 1; k < i; k++ )
            assert( Jf_CutLit(pCut, i) != Jf_CutLit(pCut, k) );
}
static inline unsigned Jf_CutGetSign( int * pCut )
{
    unsigned Sign = 0; int i; 
    for ( i = 1; i <= Jf_CutSize(pCut); i++ )
        Sign |= 1 << (Jf_CutVar(pCut, i) & 0x1F);
    return Sign;
}
static inline int Jf_CountBits( unsigned i )
{
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}
static inline int Jf_CutArr( Jf_Man_t * p, int * pCut )
{
    int i, Time = 0;
    for ( i = 1; i <= Jf_CutSize(pCut); i++ )
        Time = Abc_MaxInt( Time, Jf_ObjArr(p, Jf_CutVar(pCut, i)) );
    return Time + 1; 
}
static inline void Jf_ObjSetBestCut( int * pCuts, int * pCut, Vec_Int_t * vTemp )
{
    assert( pCuts < pCut );
    if ( ++pCuts < pCut )
    {
        int nBlock = pCut - pCuts;
        int nSize = Jf_CutSize(pCut) + 1;
        Vec_IntGrow( vTemp, nBlock );
        memmove( Vec_IntArray(vTemp), pCuts, sizeof(int) * nBlock );
        memmove( pCuts, pCut, sizeof(int) * nSize );
        memmove( pCuts + nSize, Vec_IntArray(vTemp), sizeof(int) * nBlock );
    }
}
static inline void Jf_CutRef( Jf_Man_t * p, int * pCut )
{
    int i;
    for ( i = 1; i <= Jf_CutSize(pCut); i++ )
        Gia_ObjRefIncId( p->pGia, Jf_CutVar(pCut, i) );
}
static inline void Jf_CutDeref( Jf_Man_t * p, int * pCut )
{
    int i;
    for ( i = 1; i <= Jf_CutSize(pCut); i++ )
        Gia_ObjRefDecId( p->pGia, Jf_CutVar(pCut, i) );
}
static inline float Jf_CutFlow( Jf_Man_t * p, int * pCut )
{
    float Flow = 0; int i; 
    for ( i = 1; i <= Jf_CutSize(pCut); i++ )
        Flow += Jf_ObjFlow( p, Jf_CutVar(pCut, i) );
    assert( Flow >= 0 );
    return Flow; 
}

/**Function*************************************************************

  Synopsis    [Cut merging.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Jf_CutMerge2( int * pCut0, int * pCut1, int * pCut, int LutSize )
{ 
    int * pC0 = pCut0 + 1;
    int * pC1 = pCut1 + 1;
    int * pC = pCut + 1;
    int i, k, c, s;
    // the case of the largest cut sizes
    if ( pCut0[0] == LutSize && pCut1[0] == LutSize )
    {
        for ( i = 0; i < pCut0[0]; i++ )
        {
            if ( pC0[i] != pC1[i] )
                return 0;
            pC[i] = pC0[i];
        }
        pCut[0] = LutSize;
        return 1;
    }
    // compare two cuts with different numbers
    i = k = c = s = 0;
    while ( 1 )
    {
        if ( c == LutSize ) return 0;
        if ( pC0[i] < pC1[k] )
        {
            pC[c++] = pC0[i++];
            if ( i >= pCut0[0] ) goto FlushCut1;
        }
        else if ( pC0[i] > pC1[k] )
        {
            pC[c++] = pC1[k++];
            if ( k >= pCut1[0] ) goto FlushCut0;
        }
        else
        {
            pC[c++] = pC0[i++]; k++;
            if ( i >= pCut0[0] ) goto FlushCut1;
            if ( k >= pCut1[0] ) goto FlushCut0;
        }
    }

FlushCut0:
    if ( c + pCut0[0] > LutSize + i ) return 0;
    while ( i < pCut0[0] )
        pC[c++] = pC0[i++];
    pCut[0] = c;
    return 1;

FlushCut1:
    if ( c + pCut1[0] > LutSize + k ) return 0;
    while ( k < pCut1[0] )
        pC[c++] = pC1[k++];
    pCut[0] = c;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Cut merging.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Jf_CutFindLeaf0( int * pCut, int iObj )
{
    int i;
    for ( i = 1; i <= pCut[0]; i++ )
        if ( pCut[i] == iObj )
            return i;
    return i;
}
static inline int Jf_CutIsContained0( int * pBase, int * pCut ) // check if pCut is contained pBase
{
    int i;
    for ( i = 1; i <= pCut[0]; i++ )
        if ( Jf_CutFindLeaf0(pBase, pCut[i]) > pBase[0] )
            return 0;
    return 1;
}
static inline int Jf_CutMerge0( int * pCut0, int * pCut1, int * pCut, int LutSize )
{
    int i;
    pCut[0] = pCut0[0];
    for ( i = 1; i <= pCut1[0]; i++ )
    {
        if ( Jf_CutFindLeaf0(pCut0, pCut1[i]) <= pCut0[0] )
            continue;
        if ( pCut[0] == LutSize )
            return 0;
        pCut[++pCut[0]] = pCut1[i];
    }
    memcpy( pCut + 1, pCut0 + 1, sizeof(int) * pCut0[0] );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Cut merging.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Jf_CutFindLeaf( int * pCut, int iLit )
{
    int i, nLits = Jf_CutSize(pCut);
    for ( i = 1; i <= nLits; i++ )
        if ( Abc_Lit2Var(pCut[i]) == iLit )
            return i;
    return i;
}
static inline int Jf_CutIsContained( int * pBase, int * pCut ) // check if pCut is contained pBase
{
    int i, nLits = Jf_CutSize(pCut);
    for ( i = 1; i <= nLits; i++ )
        if ( Jf_CutFindLeaf(pBase, Abc_Lit2Var(pCut[i])) > pBase[0] )
            return 0;
    return 1;
}
static inline int Jf_CutMerge8( int * pCut0, int * pCut1, int * pCut, int LutSize )
{
    int nSize0 = Jf_CutSize(pCut0);
    int nSize1 = Jf_CutSize(pCut1), i;
    pCut[0] = nSize0;
    for ( i = 1; i <= nSize1; i++ )
        if ( Jf_CutFindLeaf(pCut0, Abc_Lit2Var(pCut1[i])) > nSize0 )
        {
            if ( pCut[0] == LutSize )
                return 0;
            pCut[++pCut[0]] = pCut1[i];
        }
    memcpy( pCut + 1, pCut0 + 1, sizeof(int) * nSize0 );
    return 1;
}
static inline int Jf_CutMerge( int * pCut0, int * pCut1, int * pCut, int LutSize )
{
    int ConfigMask = 0x3FFFF; // 18 bits
    int nSize0 = Jf_CutSize(pCut0);
    int nSize1 = Jf_CutSize(pCut1);
    int i, iPlace;
    pCut[0] = nSize0;
    for ( i = 1; i <= nSize1; i++ )
    {
        iPlace = Jf_CutFindLeaf(pCut0, Abc_Lit2Var(pCut1[i]));
        if ( iPlace > nSize0 )
        {
            if ( pCut[0] == LutSize )
                return 0;
            pCut[++pCut[0]] = pCut1[i];
            iPlace = pCut[0];
        }
        ConfigMask ^= ((((i-1) & 7) ^ 7) << (3*(iPlace-1)));
        if ( pCut[iPlace] != pCut1[i] )
            ConfigMask |= (1 << (iPlace+17));
    }
    memcpy( pCut + 1, pCut0 + 1, sizeof(int) * nSize0 );
    return ConfigMask;
}


/**Function*************************************************************

  Synopsis    [Cut filtering.]

  Description [Returns the number of cuts after filtering and the last
  cut in the last entry.  If the cut is filtered, its size is set to -1.]
               
  SideEffects [This was found to be 15% slower.]

  SeeAlso     []

***********************************************************************/
int Jf_ObjCutFilter( Jf_Man_t * p, Jf_Cut_t ** pSto, int c )
{
    int k, last;
    // filter this cut using other cuts
    for ( k = 0; k < c; k++ )
        if ( pSto[c]->pCut[0] >= pSto[k]->pCut[0] && 
            (pSto[c]->Sign & pSto[k]->Sign) == pSto[k]->Sign && 
             Jf_CutIsContained(pSto[c]->pCut, pSto[k]->pCut) )
        {
                pSto[c]->pCut[0] = -1;
                return c;
        }
    // filter other cuts using this cut
    for ( k = last = 0; k < c; k++ )
        if ( !(pSto[c]->pCut[0] < pSto[k]->pCut[0] && 
              (pSto[c]->Sign & pSto[k]->Sign) == pSto[c]->Sign && 
               Jf_CutIsContained(pSto[k]->pCut, pSto[c]->pCut)) )
        {
            if ( last++ == k )
                continue;
            ABC_SWAP( Jf_Cut_t *, pSto[last-1], pSto[k] );
        }
    assert( last <= c );
    if ( last < c )
        ABC_SWAP( Jf_Cut_t *, pSto[last], pSto[c] );
    return last;
}

/**Function*************************************************************

  Synopsis    [Sorting cuts by size.]

  Description []
               
  SideEffects [Did not really help.]

  SeeAlso     []

***********************************************************************/
static inline void Jf_ObjSortCuts( Jf_Cut_t ** pSto, int nSize )
{
    int i, j, best_i;
    for ( i = 0; i < nSize-1; i++ )
    {
        best_i = i;
        for ( j = i+1; j < nSize; j++ )
            if ( pSto[j]->pCut[0] < pSto[best_i]->pCut[0] )
                best_i = j;
        ABC_SWAP( Jf_Cut_t *, pSto[i], pSto[best_i] );
    }
}

/**Function*************************************************************

  Synopsis    [Reference counting.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Jf_CutRef_rec( Jf_Man_t * p, int * pCut, int fEdge, int Limit )
{
    int i, Var, Count = 0;
    if ( Jf_CutSize(pCut) == 1 || Limit == 0 ) // terminal
        return 0;
    Jf_CutForEachVar( pCut, Var, i )
        if ( Gia_ObjRefIncId( p->pGia, Var ) == 0 )
            Count += Jf_CutRef_rec( p, Jf_ObjCutBest(p, Var), fEdge, Limit - 1 );
    return Count + (fEdge ? (1 << 16) + Jf_CutSize(pCut) : 1);
}
int Jf_CutDeref_rec( Jf_Man_t * p, int * pCut, int fEdge, int Limit )
{
    int i, Var, Count = 0;
    if ( Jf_CutSize(pCut) == 1 || Limit == 0 ) // terminal
        return 0;
    Jf_CutForEachVar( pCut, Var, i )
        if ( Gia_ObjRefDecId( p->pGia, Var ) == 0 )
            Count += Jf_CutDeref_rec( p, Jf_ObjCutBest(p, Var), fEdge, Limit - 1 );
    return Count + (fEdge ? (1 << 16) + Jf_CutSize(pCut) : 1);
}
static inline int Jf_CutElaOld( Jf_Man_t * p, int * pCut, int fEdge )
{
    int Ela1 = Jf_CutRef_rec( p, pCut, fEdge, ABC_INFINITY );
    int Ela2 = Jf_CutDeref_rec( p, pCut, fEdge, ABC_INFINITY );
    assert( Ela1 == Ela2 );
    return Ela1;
}
int Jf_CutRef2_rec( Jf_Man_t * p, int * pCut, int fEdge, int Limit )
{
    int i, Var, Count = 0;
    if ( Jf_CutSize(pCut) == 1 || Limit == 0 ) // terminal
        return 0;
    Jf_CutForEachVar( pCut, Var, i )
    {
        if ( Gia_ObjRefIncId( p->pGia, Var ) == 0 )
            Count += Jf_CutRef2_rec( p, Jf_ObjCutBest(p, Var), fEdge, Limit - 1 );
        Vec_IntPush( p->vTemp, Var );
    }
    return Count + (fEdge ? (1 << 16) + Jf_CutSize(pCut) : 1);
}
static inline int Jf_CutEla( Jf_Man_t * p, int * pCut, int fEdge )
{
    int Ela, Entry, i;
    Vec_IntClear( p->vTemp );
    Ela = Jf_CutRef2_rec( p, pCut, fEdge, JF_EDGE_LIM );
    Vec_IntForEachEntry( p->vTemp, Entry, i )
        Gia_ObjRefDecId( p->pGia, Entry );
    return Ela;
}

/**Function*************************************************************

  Synopsis    [Comparison procedures.]

  Description [Return positive value if the new cut is better than the old cut.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Jf_CutCompareDelay( Jf_Cut_t * pOld, Jf_Cut_t * pNew )
{
    if ( pOld->Time    != pNew->Time    ) return pOld->Time    - pNew->Time;
    if ( pOld->pCut[0] != pNew->pCut[0] ) return pOld->pCut[0] - pNew->pCut[0];
    if ( pOld->Flow    != pNew->Flow    ) return pOld->Flow    - pNew->Flow;
    return 0;
}
float Jf_CutCompareArea( Jf_Cut_t * pOld, Jf_Cut_t * pNew )
{
//    float Epsilon = (float)0.001;
//    if ( pOld->Flow > pNew->Flow + Epsilon ) return 1;
//    if ( pOld->Flow < pNew->Flow - Epsilon ) return -1;
    if ( pOld->Flow    != pNew->Flow    ) return pOld->Flow    - pNew->Flow;
    if ( pOld->pCut[0] != pNew->pCut[0] ) return pOld->pCut[0] - pNew->pCut[0];
    if ( pOld->Time    != pNew->Time    ) return pOld->Time    - pNew->Time;
    return 0;
}
static inline int Jf_ObjAddCutToStore( Jf_Man_t * p, Jf_Cut_t ** pSto, int c, int cMax )
{
    Jf_Cut_t * pTemp;
    int k, last, iPivot;
    // if the store is empty, add anything
    if ( c == 0 )
        return 1;
    // special case when the cut store is full and last cut is better than new cut
    if ( c == cMax && p->pCutCmp(pSto[c-1], pSto[c]) <= 0 )
        return c;
    // find place of the given cut in the store
    assert( c <= cMax );
    for ( iPivot = c-1; iPivot >= 0; iPivot-- )
        if ( p->pCutCmp(pSto[iPivot], pSto[c]) < 0 ) // iPivot-th cut is better than new cut
            break;
    // filter this cut using other cuts
    for ( k = 0; k <= iPivot; k++ )
        if ( pSto[c]->pCut[0] >= pSto[k]->pCut[0] && 
            (pSto[c]->Sign & pSto[k]->Sign) == pSto[k]->Sign && 
             Jf_CutIsContained(pSto[c]->pCut, pSto[k]->pCut) )
                return c;
    // insert this cut after iPivot
    pTemp = pSto[c];
    for ( ++iPivot, k = c++; k > iPivot; k-- )
        pSto[k] = pSto[k-1];
    pSto[iPivot] = pTemp;
    // filter other cuts using this cut
    for ( k = last = iPivot+1; k < c; k++ )
        if ( !(pSto[iPivot]->pCut[0] <= pSto[k]->pCut[0] && 
              (pSto[iPivot]->Sign & pSto[k]->Sign) == pSto[iPivot]->Sign && 
               Jf_CutIsContained(pSto[k]->pCut, pSto[iPivot]->pCut)) )
        {
            if ( last++ == k )
                continue;
            ABC_SWAP( Jf_Cut_t *, pSto[last-1], pSto[k] );
        }
    c = last;
    // remove the last cut if too many
    if ( c == cMax + 1 )
        return c - 1;
    return c;
}
static inline void Jf_ObjPrintStore( Jf_Man_t * p, Jf_Cut_t ** pSto, int c )
{
    int i;
    for ( i = 0; i < c; i++ )
    {
        printf( "Area =%9.5f  ", pSto[i]->Flow );
        printf( "Time = %5d   ", pSto[i]->Time );
        printf( "  " );
        Jf_CutPrint( pSto[i]->pCut );
    }
    printf( "\n" );
}
static inline void Jf_ObjCheckPtrs( Jf_Cut_t ** pSto, int c )
{
    int i, k;
    for ( i = 1; i < c; i++ )
        for ( k = 0; k < i; k++ )
            assert( pSto[k] != pSto[i] );
}
static inline void Jf_ObjCheckStore( Jf_Man_t * p, Jf_Cut_t ** pSto, int c, int iObj )
{
    int i, k;
    for ( i = 1; i < c; i++ )
        assert( p->pCutCmp(pSto[i-1], pSto[i]) <= 0 );
    for ( i = 1; i < c; i++ )
        for ( k = 0; k < i; k++ )
        {
            assert( !Jf_CutIsContained(pSto[k]->pCut, pSto[i]->pCut) );
            assert( !Jf_CutIsContained(pSto[i]->pCut, pSto[k]->pCut) );
        }
}

/**Function*************************************************************

  Synopsis    [Cut enumeration.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Jf_ObjAssignCut( Jf_Man_t * p, Gia_Obj_t * pObj )
{
    int iObj = Gia_ObjId(p->pGia, pObj);
    int pClause[3] = { 1, (2 << 5) | 1, Jf_ObjLit(iObj) }; // set function
    assert( Gia_ObjIsCi(pObj) || Gia_ObjIsBuf(pObj) );
    Vec_IntWriteEntry( &p->vCuts, iObj, Vec_SetAppend( &p->pMem, pClause, 3 ) );
}
static inline void Jf_ObjPropagateBuf( Jf_Man_t * p, Gia_Obj_t * pObj, int fReverse )
{
    int iObj = Gia_ObjId( p->pGia, pObj );
    int iFanin = Gia_ObjFaninId0( pObj, iObj );
    assert( 0 );
    assert( Gia_ObjIsBuf(pObj) );
    if ( fReverse )
        ABC_SWAP( int, iObj, iFanin );
    Vec_IntWriteEntry( &p->vArr,  iObj, Jf_ObjArr(p, iFanin) );
    Vec_FltWriteEntry( &p->vFlow, iObj, Jf_ObjFlow(p, iFanin) );
}
static inline void Jf_ObjBypassNode( Gia_Man_t * p, Gia_Obj_t * pObj, int * pCut, Vec_Int_t * vTemp )
{
    assert( !pObj->fMark0 );
    assert( Gia_ObjFanin0(pObj)->fMark0 );
    assert( Gia_ObjFanin1(pObj)->fMark0 );
    Vec_IntClear( vTemp );
    Vec_IntPushUnique( vTemp, Jf_ObjLit(Gia_ObjFaninId0p(p, Gia_ObjFanin0(pObj))) );
    Vec_IntPushUnique( vTemp, Jf_ObjLit(Gia_ObjFaninId1p(p, Gia_ObjFanin0(pObj))) );
    Vec_IntPushUnique( vTemp, Jf_ObjLit(Gia_ObjFaninId0p(p, Gia_ObjFanin1(pObj))) );
    Vec_IntPushUnique( vTemp, Jf_ObjLit(Gia_ObjFaninId1p(p, Gia_ObjFanin1(pObj))) );
    assert( Vec_IntSize(vTemp) == 2 || Vec_IntSize(vTemp) == 3 );
    pCut[0] = Vec_IntSize(vTemp); 
    memcpy( pCut + 1, Vec_IntArray(vTemp), sizeof(int) * Vec_IntSize(vTemp) );
}
void Jf_ObjComputeCuts( Jf_Man_t * p, Gia_Obj_t * pObj )
{
    int        LutSize = p->pPars->nLutSize;
    int        CutNum = p->pPars->nCutNum;
    int        iObj = Gia_ObjId(p->pGia, pObj);
    unsigned   Sign0[JF_CUT_MAX+1]; // signatures of the first cut
    unsigned   Sign1[JF_CUT_MAX+1]; // signatures of the second cut
    Jf_Cut_t   Sto[JF_CUT_MAX+1];   // cut storage
    Jf_Cut_t * pSto[JF_CUT_MAX+1];  // pointers to cut storage
    int *      pCut0, * pCut1, * pCuts0, * pCuts1;
    int        Config, i, k, c = 0;
    // prepare cuts
    for ( i = 0; i <= CutNum; i++ )
        pSto[i] = Sto + i;
    // compute signatures
    pCuts0 = Jf_ObjCuts( p, Gia_ObjFaninId0(pObj, iObj) );
    Jf_ObjForEachCut( pCuts0, pCut0, i )
        Sign0[i] = Jf_CutGetSign( pCut0 );
    // compute signatures
    pCuts1 = Jf_ObjCuts( p, Gia_ObjFaninId1(pObj, iObj) );
    Jf_ObjForEachCut( pCuts1, pCut1, i )
        Sign1[i] = Jf_CutGetSign( pCut1 );
    // merge cuts
    p->CutCount[0] += pCuts0[0] * pCuts1[0];
    Jf_ObjForEachCut( pCuts0, pCut0, i )
    Jf_ObjForEachCut( pCuts1, pCut1, k )
    {
        if ( Jf_CountBits(Sign0[i] | Sign1[k]) > LutSize )
            continue;
        p->CutCount[1]++;        
        if ( !(Config = Jf_CutMerge(pCut0, pCut1, pSto[c]->pCut, LutSize)) )
            continue;
        if ( p->pPars->fCutMin )
        {
            int iDsdLit0 = Abc_LitNotCond( Jf_CutFunc(pCut0), Gia_ObjFaninC0(pObj) );
            int iDsdLit1 = Abc_LitNotCond( Jf_CutFunc(pCut1), Gia_ObjFaninC1(pObj) );
            pSto[c]->iFunc = Sdm_ManComputeFunc( p->pDsd, iDsdLit0, iDsdLit1, pSto[c]->pCut, Config, 0 );
//            pSto[c]->iFunc = Sdm_ManComputeFunc( p->pDsd, iDsdLit0, iDsdLit1, NULL, Config, 0 );
            if ( pSto[c]->iFunc == -1 )
                continue;
            pSto[c]->Cost = 0;//Sdm_ManReadCnfSize( p->pDsd, Abc_Lit2Var(pSto[c]->iFunc) );
        }
//        Jf_CutCheck( pSto[c]->pCut );
        p->CutCount[2]++;
        pSto[c]->Sign = p->pPars->fCutMin ? Jf_CutGetSign(pSto[c]->pCut) : Sign0[i] | Sign1[k];
        pSto[c]->Time = p->pPars->fAreaOnly ? 0 : Jf_CutArr(p, pSto[c]->pCut);
        pSto[c]->Flow = Jf_CutFlow(p, pSto[c]->pCut);
        c = Jf_ObjAddCutToStore( p, pSto, c, CutNum );
        assert( c <= CutNum );
    }
//    Jf_ObjCheckStore( p, pSto, c, iObj );
    // fix the case when both fanins have no unit cuts
    if ( c == 0 )
    {
        Jf_ObjBypassNode( p->pGia, pObj, pSto[0]->pCut, p->vTemp );
        pSto[0]->Sign = Jf_CutGetSign( pSto[0]->pCut );
        pSto[0]->Time = p->pPars->fAreaOnly ? 0 : Jf_CutArr(p, pSto[0]->pCut);
        pSto[0]->Flow = Jf_CutFlow(p, pSto[0]->pCut);
        pSto[c]->iFunc = (pSto[0]->pCut[0] == 2) ? 6 : 18; // set function
        pSto[c]->Cost = 4;
        c = 1;
    }
    // add elementary cut
    if ( !pObj->fMark0 )
        pSto[c]->iFunc = 2, pSto[c]->pCut[0] = 1, pSto[c]->pCut[1] = Jf_ObjLit(iObj), c++; // set function
    // reorder cuts
//    Jf_ObjSortCuts( pSto + 1, c - 1 );
//    Jf_ObjCheckPtrs( pSto, CutNum );
    p->CutCount[3] += c;
    // save best info
    Vec_IntWriteEntry( &p->vArr,  iObj, pSto[0]->Time );
    Vec_FltWriteEntry( &p->vFlow, iObj, (pSto[0]->Flow + 1) / Jf_ObjRefs(p, iObj) );
//    Vec_FltWriteEntry( &p->vFlow, iObj, (pSto[0]->Flow + ((1 << 6) + pSto[0]->pCut[0])) / Jf_ObjRefs(p, iObj) );
    // add cuts to storage cuts
    Vec_IntClear( p->vTemp );
    Vec_IntPush( p->vTemp, c );
    for ( i = 0; i < c; i++ )
    {
        assert( pSto[i]->pCut[0] <= 6 );
        assert( pSto[i]->iFunc < (1<<11) );
        Vec_IntPush( p->vTemp, (pSto[i]->Cost << 16) | (pSto[i]->iFunc << 5) | pSto[i]->pCut[0] );
        for ( k = 1; k <= pSto[i]->pCut[0]; k++ )
            Vec_IntPush( p->vTemp, pSto[i]->pCut[k] );
    }
    Vec_IntWriteEntry( &p->vCuts, iObj, Vec_SetAppend(&p->pMem, Vec_IntArray(p->vTemp), Vec_IntSize(p->vTemp)) );
}
void Jf_ManComputeCuts( Jf_Man_t * p )
{
    Gia_Obj_t * pObj; int i;
    if ( p->pPars->fVerbose )
    {
        printf( "Aig: CI = %d  CO = %d  AND = %d    ", Gia_ManCiNum(p->pGia), Gia_ManCoNum(p->pGia), Gia_ManAndNum(p->pGia) );
        printf( "LutSize = %d  CutMax = %d  Rounds = %d\n", p->pPars->nLutSize, p->pPars->nCutNum, p->pPars->nRounds );
        printf( "Computing cuts...\r" );
        fflush( stdout );
    }
    Gia_ManForEachObj( p->pGia, pObj, i )
    {
        if ( Gia_ObjIsCi(pObj) || Gia_ObjIsBuf(pObj) )
            Jf_ObjAssignCut( p, pObj );
        if ( Gia_ObjIsBuf(pObj) )
            Jf_ObjPropagateBuf( p, pObj, 0 );
        else if ( Gia_ObjIsAnd(pObj) )
            Jf_ObjComputeCuts( p, pObj );
    }
    if ( p->pPars->fVerbose )
    {
        printf( "CutPair = %lu  ", p->CutCount[0] );
        printf( "Merge = %lu  ",   p->CutCount[1] );
        printf( "Eval = %lu  ",    p->CutCount[2] );
        printf( "Cut = %lu  ",     p->CutCount[3] );
        Abc_PrintTime( 1, "Time",  Abc_Clock() - p->clkStart );
        printf( "Memory:  " );
        printf( "Gia = %.2f MB  ", Gia_ManMemory(p->pGia) / (1<<20) );
        printf( "Man = %.2f MB  ", 6.0 * sizeof(int) * Gia_ManObjNum(p->pGia) / (1<<20) );
        printf( "Cuts = %.2f MB",  Vec_ReportMemory(&p->pMem) / (1<<20) );
        if ( p->nCoarse )
        printf( "   Coarse = %d (%.1f %%)",  p->nCoarse, 100.0 * p->nCoarse / Gia_ManObjNum(p->pGia) );
        printf( "\n" );
        fflush( stdout );
    }
}


/**Function*************************************************************

  Synopsis    [Computing delay/area.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Jf_ManComputeDelay( Jf_Man_t * p, int fEval )
{
    Gia_Obj_t * pObj; 
    int i, Delay = 0;
    if ( fEval )
    {
        Gia_ManForEachObj( p->pGia, pObj, i )
            if ( Gia_ObjIsBuf(pObj) )
                Jf_ObjPropagateBuf( p, pObj, 0 );
            else if ( Gia_ObjIsAnd(pObj) && Gia_ObjRefNum(p->pGia, pObj) > 0 )
                Vec_IntWriteEntry( &p->vArr, i, Jf_CutArr(p, Jf_ObjCutBest(p, i)) );
    }
    Gia_ManForEachCoDriver( p->pGia, pObj, i )
    {
        assert( Gia_ObjRefNum(p->pGia, pObj) > 0 );
        Delay = Abc_MaxInt( Delay, Jf_ObjArr(p, Gia_ObjId(p->pGia, pObj)) );
    }
    return Delay;
}
int Jf_ManComputeRefs( Jf_Man_t * p )
{
    Gia_Obj_t * pObj; 
    float nRefsNew; int i;
    float * pRefs = Vec_FltArray(&p->vRefs);
    float * pFlow = Vec_FltArray(&p->vFlow);
    assert( p->pGia->pRefs != NULL );
    memset( p->pGia->pRefs, 0, sizeof(int) * Gia_ManObjNum(p->pGia) );
    p->pPars->Area = p->pPars->Edge = 0;
    Gia_ManForEachObjReverse( p->pGia, pObj, i )
    {
        if ( Gia_ObjIsCo(pObj) || Gia_ObjIsBuf(pObj) )
            Gia_ObjRefInc( p->pGia, Gia_ObjFanin0(pObj) );
        else if ( Gia_ObjIsAnd(pObj) && Gia_ObjRefNum(p->pGia, pObj) > 0 )
        {
            assert( !pObj->fMark0 );
            Jf_CutRef( p, Jf_ObjCutBest(p, i) );
            p->pPars->Edge += Jf_CutSize(Jf_ObjCutBest(p, i));
            p->pPars->Area++;
        }
        // blend references and normalize flow
        nRefsNew = Abc_MaxFloat( 1, 0.25 * pRefs[i] + 0.75 * p->pGia->pRefs[i] );
        pFlow[i] = pFlow[i] * pRefs[i] / nRefsNew;
        pRefs[i] = nRefsNew;
        assert( pFlow[i] >= 0 );
    }
    p->pPars->Delay = Jf_ManComputeDelay( p, 1 );
    return p->pPars->Area;
}

/**Function*************************************************************

  Synopsis    [Mapping rounds.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Jf_ObjComputeBestCut( Jf_Man_t * p, Gia_Obj_t * pObj, int fEdge, int fEla )
{
    int i, iObj = Gia_ObjId( p->pGia, pObj );
    int * pCuts = Jf_ObjCuts( p, iObj );
    int * pCut, * pCutBest = NULL;
    int Time = ABC_INFINITY, TimeBest = ABC_INFINITY;
    float Area, AreaBest = ABC_INFINITY;
    Jf_ObjForEachCut( pCuts, pCut, i )
    {
        if ( Jf_CutSize(pCut) == 1 && Jf_CutVar(pCut, 1) == iObj ) continue;
        Area = fEla ? Jf_CutEla(p, pCut, fEdge) : Jf_CutFlow(p, pCut);
        if ( pCutBest == NULL || AreaBest > Area || (AreaBest == Area && TimeBest > (Time = Jf_CutArr(p, pCut))) )
            pCutBest = pCut, AreaBest = Area, TimeBest = Time;
    }
    Vec_IntWriteEntry( &p->vArr,  iObj, Jf_CutArr(p, pCutBest) );
    if ( !fEla )
    Vec_FltWriteEntry( &p->vFlow, iObj, (AreaBest + (fEdge ? Jf_CutSize(pCut) : 1)) / Jf_ObjRefs(p, iObj) );
    Jf_ObjSetBestCut( pCuts, pCutBest, p->vTemp );
//    Jf_CutPrint( Jf_ObjCutBest(p, iObj) ); printf( "\n" );
}
void Jf_ManPropagateFlow( Jf_Man_t * p, int fEdge )
{
    Gia_Obj_t * pObj; 
    int i;
    Gia_ManForEachObj( p->pGia, pObj, i )
        if ( Gia_ObjIsBuf(pObj) )
            Jf_ObjPropagateBuf( p, pObj, 0 );
        else if ( Gia_ObjIsAnd(pObj) && !pObj->fMark0 )
            Jf_ObjComputeBestCut( p, pObj, fEdge, 0 );
    Jf_ManComputeRefs( p );
}
void Jf_ManPropagateEla( Jf_Man_t * p, int fEdge )
{
    Gia_Obj_t * pObj; 
    int i, CostBef, CostAft;
    p->pPars->Area = p->pPars->Edge = 0;
    Gia_ManForEachObjReverse( p->pGia, pObj, i )
        if ( Gia_ObjIsBuf(pObj) )
            Jf_ObjPropagateBuf( p, pObj, 1 );
        else if ( Gia_ObjIsAnd(pObj) && Gia_ObjRefNum(p->pGia, pObj) > 0 )
        {
            assert( !pObj->fMark0 );
            CostBef = Jf_CutDeref_rec( p, Jf_ObjCutBest(p, i), fEdge, ABC_INFINITY );
            Jf_ObjComputeBestCut( p, pObj, fEdge, 1 );
            CostAft = Jf_CutRef_rec( p, Jf_ObjCutBest(p, i), fEdge, ABC_INFINITY );
//            assert( CostBef >= CostAft ); // does not hold because of JF_EDGE_LIM
            p->pPars->Edge += Jf_CutSize(Jf_ObjCutBest(p, i));
            p->pPars->Area++;
        }
    p->pPars->Delay = Jf_ManComputeDelay( p, 1 );
}
void Jf_ManDeriveMapping( Jf_Man_t * p )
{
    Vec_Int_t * vMapping;
    Gia_Obj_t * pObj; 
    int i, k, * pCut;
    vMapping = Vec_IntAlloc( Gia_ManObjNum(p->pGia) + p->pPars->Edge + p->pPars->Area * 2 );
    Vec_IntFill( vMapping, Gia_ManObjNum(p->pGia), 0 );
    Gia_ManForEachAnd( p->pGia, pObj, i )
    {
        if ( Gia_ObjIsBuf(pObj) || Gia_ObjRefNum(p->pGia, pObj) == 0 )
            continue;
        pCut = Jf_ObjCutBest( p, i );
        Vec_IntWriteEntry( vMapping, i, Vec_IntSize(vMapping) );
        assert( Jf_CutSize(pCut) <= 6 );
        Vec_IntPush( vMapping, Jf_CutSize(pCut) );
        for ( k = 1; k <= Jf_CutSize(pCut); k++ )
            Vec_IntPush( vMapping, Jf_CutVar(pCut, k) );
        Vec_IntPush( vMapping, i );
    }
    assert( Vec_IntSize(vMapping) == Vec_IntCap(vMapping) );
    p->pGia->vMapping = vMapping;
//    Gia_ManMappingVerify( p->pGia );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Jf_ManSetDefaultPars( Jf_Par_t * pPars )
{
    memset( pPars, 0, sizeof(Jf_Par_t) );
    pPars->nLutSize     =  6;
    pPars->nCutNum      =  8;
    pPars->nRounds      =  1;
    pPars->DelayTarget  = -1;
    pPars->fAreaOnly    =  1;
    pPars->fCoarsen     =  0;
    pPars->fCutMin      =  0;
    pPars->fVerbose     =  0;
    pPars->fVeryVerbose =  0;
    pPars->nLutSizeMax  =  JF_LEAF_MAX;
    pPars->nCutNumMax   =  JF_CUT_MAX;
}
void Jf_ManPrintStats( Jf_Man_t * p, char * pTitle )
{
    if ( !p->pPars->fVerbose )
        return;
    printf( "%s :  ", pTitle );
    printf( "Level =%6d   ", p->pPars->Delay );
    printf( "Area =%9d   ",  p->pPars->Area );
    printf( "Edge =%9d   ",  p->pPars->Edge );
    Abc_PrintTime( 1, "Time", Abc_Clock() - p->clkStart );
    fflush( stdout );
}
Gia_Man_t * Jf_ManPerformMapping( Gia_Man_t * pGia, Jf_Par_t * pPars )
{
    Jf_Man_t * p; int i;
    p = Jf_ManAlloc( pGia, pPars );
    p->pCutCmp = pPars->fAreaOnly ? Jf_CutCompareArea : Jf_CutCompareDelay;
    Jf_ManComputeCuts( p );
    Jf_ManComputeRefs( p );                  Jf_ManPrintStats( p, "Start" );
    for ( i = 0; i < pPars->nRounds; i++ )
    {
        Jf_ManPropagateFlow( p, 0 );         Jf_ManPrintStats( p, "Flow " );
        Jf_ManPropagateEla( p, 0 );          Jf_ManPrintStats( p, "Area " );
        Jf_ManPropagateEla( p, 1 );          Jf_ManPrintStats( p, "Edge " );
    }
    Jf_ManDeriveMapping( p );
    Jf_ManFree( p );
    return pGia;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

