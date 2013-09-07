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
    int              pCut[JF_LEAF_MAX+1];
};

typedef struct Jf_Man_t_ Jf_Man_t; 
struct Jf_Man_t_
{
    Gia_Man_t *      pGia;        // user's manager
    Jf_Par_t *       pPars;       // users parameter
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
};

static inline int    Jf_ObjCutH( Jf_Man_t * p, int i )    { return Vec_IntEntry(&p->vCuts, i);                       }
static inline int *  Jf_ObjCuts( Jf_Man_t * p, int i )    { return (int *)Vec_SetEntry(&p->pMem, Jf_ObjCutH(p, i));  }
static inline int *  Jf_ObjCutBest( Jf_Man_t * p, int i ) { return Jf_ObjCuts(p, i) + 1;                             }
static inline int    Jf_ObjArr( Jf_Man_t * p, int i )     { return Vec_IntEntry(&p->vArr, i);                        }
static inline int    Jf_ObjDep( Jf_Man_t * p, int i )     { return Vec_IntEntry(&p->vDep, i);                        }
static inline float  Jf_ObjFlow( Jf_Man_t * p, int i )    { return Vec_FltEntry(&p->vFlow, i);                       }
static inline float  Jf_ObjRefs( Jf_Man_t * p, int i )    { return Vec_FltEntry(&p->vRefs, i);                       }

#define Jf_ObjForEachCut( pList, pCut, i )   for ( i = 0, pCut = pList + 1; i < pList[0]; i++, pCut += pCut[0] + 1 )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computing references while discounting XOR/MUX.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float * Jf_ManInitRefs( Gia_Man_t * p )
{
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
    Vec_IntFill( &p->vCuts, Gia_ManObjNum(pGia), 0 );
    Vec_IntFill( &p->vArr,  Gia_ManObjNum(pGia), 0 );
    Vec_IntFill( &p->vDep,  Gia_ManObjNum(pGia), 0 );
    Vec_FltFill( &p->vFlow, Gia_ManObjNum(pGia), 0 );
    p->vRefs.nCap = p->vRefs.nSize = Gia_ManObjNum(pGia);
    p->vRefs.pArray = Jf_ManInitRefs( pGia );
    Vec_SetAlloc_( &p->pMem, 20 );
    p->vTemp     = Vec_IntAlloc( 1000 );
    p->clkStart  = Abc_Clock();
    return p;
}
void Jf_ManFree( Jf_Man_t * p )
{
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
    printf( "%d {", pCut[0] );
    for ( i = 1; i <= pCut[0]; i++ )
        printf( " %d", pCut[i] );
    printf( " }\n" );
}
static inline void Jf_ObjCutPrint( int * pCuts )
{
    int i, * pCut; 
    Jf_ObjForEachCut( pCuts, pCut, i )
        Jf_CutPrint( pCut );
    printf( "\n" );
}
static inline unsigned Jf_CutGetSign( int * pCut )
{
    unsigned Sign = 0; int i; 
    for ( i = 1; i <= pCut[0]; i++ )
        Sign |= 1 << (pCut[i] & 31);
    return Sign;
}
static inline int Jf_CountBits( unsigned i )
{
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}
static inline int Jf_CutFindLeaf( int * pCut, int iObj )
{
    int i;
    for ( i = 1; i <= pCut[0]; i++ )
        if ( pCut[i] == iObj )
            return 1;
    return 0;
}
static inline int Jf_CutMerge( int * pCut0, int * pCut1, int * pCut, int LutSize )
{
    int i;
    if ( pCut0[0] > pCut1[0] )
        ABC_SWAP( int *, pCut0, pCut1 );
    assert( pCut0[0] <= pCut1[0] );
    pCut[0] = pCut1[0];
    for ( i = 1; i <= pCut0[0]; i++ )
    {
        if ( Jf_CutFindLeaf(pCut1, pCut0[i]) )
            continue;
        if ( pCut[0] == LutSize )
            return 1;
        pCut[++pCut[0]] = pCut0[i];
    }
    memcpy( pCut + 1, pCut1 + 1, sizeof(int) * pCut1[0] );
//    Vec_IntSelectSort( pCut + 1, pCut[0] );
    if ( 0 )
    {
        int i, k;
        for ( i = 1; i < pCut[0]; i++ )
            for ( k = 0; k < i; k++ )
                assert( pCut[i+1] != pCut[k+1] );
    }
    return 0;
}
static inline int Jf_CutIsContained( int * pBase, int * pCut ) // check if pCut is contained pBase
{
    int i;
    for ( i = 1; i <= pCut[0]; i++ )
        if ( !Jf_CutFindLeaf(pBase, pCut[i]) )
            return 0;
    return 1;
}
static inline int Jf_CutArr( Jf_Man_t * p, int * pCut )
{
    int i, Time = 0;
    for ( i = 1; i <= pCut[0]; i++ )
        Time = Abc_MaxInt( Time, Jf_ObjArr(p, pCut[i]) );
    return Time + 1; 
}
static inline void Jf_ObjSetBestCut( int * pCuts, int * pCut, Vec_Int_t * vTemp )
{
    int * pTemp, nSize;
    assert( pCuts < pCut );
    if ( pCuts + 1 == pCut )
        return;
    Vec_IntClear( vTemp );
    for ( pTemp = pCuts + 1; pTemp < pCut; pTemp++ )
        Vec_IntPush( vTemp, *pTemp );
    nSize = pCut[0] + 1;
    memcpy( pCuts + 1, pCut, sizeof(int) * nSize );
    memcpy( pCuts + 1 + nSize, Vec_IntArray(vTemp), sizeof(int) * Vec_IntSize(vTemp) );
}
static inline void Jf_CutRef( Jf_Man_t * p, int * pCut )
{
    int i;
    for ( i = 1; i <= pCut[0]; i++ )
        Gia_ObjRefIncId( p->pGia, pCut[i] );
}
static inline void Jf_CutDeref( Jf_Man_t * p, int * pCut )
{
    int i;
    for ( i = 1; i <= pCut[0]; i++ )
        Gia_ObjRefDecId( p->pGia, pCut[i] );
}
static inline float Jf_CutFlow( Jf_Man_t * p, int * pCut )
{
    float Flow = 0; int i; 
    for ( i = 1; i <= pCut[0]; i++ )
        Flow += Jf_ObjFlow( p, pCut[i] );
    return Flow; 
}

/**Function*************************************************************

  Synopsis    [Reference counting.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Jf_CutRef_rec( Jf_Man_t * p, int * pCut, int fEdge, int Limit )
{
    int i, Count = 0;
    if ( pCut[0] == 1 || Limit == 0 ) // terminal
        return 0;
    for ( i = 1; i <= pCut[0]; i++ )
        if ( Gia_ObjRefIncId( p->pGia, pCut[i] ) == 0 )
            Count += Jf_CutRef_rec( p, Jf_ObjCutBest(p, pCut[i]), fEdge, Limit - 1 );
    return Count + (fEdge ? pCut[0] : 1);
}
int Jf_CutDeref_rec( Jf_Man_t * p, int * pCut, int fEdge, int Limit )
{
    int i, Count = 0;
    if ( pCut[0] == 1 || Limit == 0 ) // terminal
        return 0;
    for ( i = 1; i <= pCut[0]; i++ )
        if ( Gia_ObjRefDecId( p->pGia, pCut[i] ) == 0 )
            Count += Jf_CutDeref_rec( p, Jf_ObjCutBest(p, pCut[i]), fEdge, Limit - 1 );
    return Count + (fEdge ? pCut[0] : 1);
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
    int i, Count = 0;
    if ( pCut[0] == 1 || Limit == 0 ) // terminal
        return 0;
    for ( i = 1; i <= pCut[0]; i++ )
    {
        Vec_IntPush( p->vTemp, pCut[i] );
        if ( Gia_ObjRefIncId( p->pGia, pCut[i] ) == 0 )
            Count += Jf_CutRef2_rec( p, Jf_ObjCutBest(p, pCut[i]), fEdge, Limit - 1 );
    }
    return Count + (fEdge ? pCut[0] : 1);
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
    int pStore[3] = { 1, 1, iObj };
    assert( Gia_ObjIsCi(pObj) || Gia_ObjIsBuf(pObj) );
    Vec_IntWriteEntry( &p->vCuts, iObj, Vec_SetAppend( &p->pMem, pStore, 3 ) );
}
static inline void Jf_ObjPropagateBuf( Jf_Man_t * p, Gia_Obj_t * pObj, int fReverse )
{
    int iObj = Gia_ObjId( p->pGia, pObj );
    int iFanin = Gia_ObjFaninId0( pObj, iObj );
    assert( Gia_ObjIsBuf(pObj) );
    if ( fReverse )
        ABC_SWAP( int, iObj, iFanin );
    Vec_IntWriteEntry( &p->vArr,  iObj, Jf_ObjArr(p, iFanin) );
    Vec_FltWriteEntry( &p->vFlow, iObj, Jf_ObjFlow(p, iFanin) );
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
    int        i, k, c = 0;
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
        if ( Jf_CutMerge(pCut0, pCut1, pSto[c]->pCut, LutSize) )
            continue;
        p->CutCount[2]++;
        pSto[c]->Sign = Sign0[i] | Sign1[k];
        pSto[c]->Time = p->pPars->fAreaOnly ? 0 : Jf_CutArr(p, pSto[c]->pCut);
        pSto[c]->Flow = Jf_CutFlow(p, pSto[c]->pCut);
        c = Jf_ObjAddCutToStore( p, pSto, c, CutNum );
        assert( c <= CutNum );
    }
//    Jf_ObjCheckPtrs( pSto, CutNum );
//    Jf_ObjCheckStore( p, pSto, c, iObj );
    p->CutCount[3] += c;
    // save best info
    Vec_IntWriteEntry( &p->vArr,  iObj, pSto[0]->Time );
    Vec_FltWriteEntry( &p->vFlow, iObj, (pSto[0]->Flow + 1) / Jf_ObjRefs(p, iObj) );
    // collect cuts
    Vec_IntClear( p->vTemp );
    Vec_IntPush( p->vTemp, c + !pObj->fMark0 );
    for ( i = 0; i < c; i++ )
        for ( k = 0; k <= pSto[i]->pCut[0]; k++ )
            Vec_IntPush( p->vTemp, pSto[i]->pCut[k] );
    // add elementary cut
    if ( !pObj->fMark0 )
        Vec_IntPush( p->vTemp, 1 ), Vec_IntPush( p->vTemp, iObj );
    // save cuts
    Vec_IntWriteEntry( &p->vCuts, iObj, Vec_SetAppend(&p->pMem, Vec_IntArray(p->vTemp), Vec_IntSize(p->vTemp)) );
}
void Jf_ManComputeCuts( Jf_Man_t * p )
{
    Gia_Obj_t * pObj; int i;
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
        printf( "Aig: CI = %d  CO = %d  AND = %d    ", Gia_ManCiNum(p->pGia), Gia_ManCoNum(p->pGia), Gia_ManAndNum(p->pGia) );
        printf( "LutSize = %d  CutMax = %d  Rounds = %d\n", p->pPars->nLutSize, p->pPars->nCutNum, p->pPars->nRounds );
        printf( "CutPair = %d  ",  p->CutCount[0] );
        printf( "Merge = %d  ",    p->CutCount[1] );
        printf( "Eval = %d  ",     p->CutCount[2] );
        printf( "Cut = %d  ",      p->CutCount[3] );
        Abc_PrintTime( 1, "Time",  Abc_Clock() - p->clkStart );
        printf( "Memory:  " );
        printf( "Gia = %.2f MB  ", Gia_ManMemory(p->pGia) / (1<<20) );
        printf( "Man = %.2f MB  ", 6.0 * sizeof(int) * Gia_ManObjNum(p->pGia) / (1<<20) );
        printf( "Cuts = %.2f MB",  Vec_ReportMemory(&p->pMem) / (1<<20) );
        printf( "\n" );
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
            Jf_CutRef( p, Jf_ObjCutBest(p, i) );
            p->pPars->Edge += Jf_ObjCutBest(p, i)[0];
            p->pPars->Area++;
        }
        // blend references and normalize flow
        nRefsNew = Abc_MaxFloat( 1.0, 0.25 * pRefs[i] + 0.75 * p->pGia->pRefs[i] );
        pFlow[i] = pFlow[i] * pRefs[i] / nRefsNew;
        pRefs[i] = nRefsNew;
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
        if ( pCut[0] == 1 ) continue;
        Area = fEla ? Jf_CutEla(p, pCut, fEdge) : Jf_CutFlow(p, pCut);
        if ( pCutBest == NULL || AreaBest > Area || (AreaBest == Area && TimeBest > (Time = Jf_CutArr(p, pCut))) )
            pCutBest = pCut, AreaBest = Area, TimeBest = Time;
    }
    Vec_IntWriteEntry( &p->vArr,  iObj, Jf_CutArr(p, pCutBest) );
    if ( !fEla )
    Vec_FltWriteEntry( &p->vFlow, iObj, (AreaBest + (fEdge ? pCut[0] : 1)) / Jf_ObjRefs(p, iObj) );
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
        else if ( Gia_ObjIsAnd(pObj) )
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
            CostBef = Jf_CutDeref_rec( p, Jf_ObjCutBest(p, i), fEdge, ABC_INFINITY );
            Jf_ObjComputeBestCut( p, pObj, fEdge, 1 );
            CostAft = Jf_CutRef_rec( p, Jf_ObjCutBest(p, i), fEdge, ABC_INFINITY );
//            assert( CostBef >= CostAft ); // does not hold because of JF_EDGE_LIM
            p->pPars->Edge += Jf_ObjCutBest(p, i)[0];
            p->pPars->Area++;
        }
    p->pPars->Delay = Jf_ManComputeDelay( p, 1 );
}
void Jf_ManDeriveMapping( Jf_Man_t * p )
{
    Vec_Int_t * vMapping;
    Gia_Obj_t * pObj; 
    int i, k, * pCut;
    vMapping = Vec_IntStart( Gia_ManObjNum(p->pGia) );
    Gia_ManForEachAnd( p->pGia, pObj, i )
    {
        if ( Gia_ObjIsBuf(pObj) || Gia_ObjRefNum(p->pGia, pObj) == 0 )
            continue;
        pCut = Jf_ObjCutBest( p, i );
        Vec_IntWriteEntry( vMapping, i, Vec_IntSize(vMapping) );
        for ( k = 0; k <= pCut[0]; k++ )
            Vec_IntPush( vMapping, pCut[k] );
        Vec_IntPush( vMapping, i );
    }
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
    printf( "Time =%6d   ", p->pPars->Delay );
    printf( "Area =%8d   ", p->pPars->Area );
    printf( "Edge =%8d   ", p->pPars->Edge );
    Abc_PrintTime( 1, "Time", Abc_Clock() - p->clkStart );
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

