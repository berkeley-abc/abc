/**CFile****************************************************************

  FileName    [cecClass.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinatinoal equivalence checking.]

  Synopsis    [Equivalence class representation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecClass.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cecInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline int        Cec_ObjRepr( Cec_ManCsw_t * p, int Id )               { return p->pObjs[Id].iRepr;               }
static inline void       Cec_ObjSetRepr( Cec_ManCsw_t * p, int Id, int Num )   { p->pObjs[Id].iRepr = Num;                }

static inline int        Cec_ObjProved( Cec_ManCsw_t * p, int Id )             { return p->pObjs[Id].iProved;             }
static inline void       Cec_ObjSetProved( Cec_ManCsw_t * p, int Id )          { p->pObjs[Id].iProved = 1;                }

static inline int        Cec_ObjFailed( Cec_ManCsw_t * p, int Id )             { return p->pObjs[Id].iFailed;             }
static inline void       Cec_ObjSetFailed( Cec_ManCsw_t * p, int Id )          { p->pObjs[Id].iFailed = 1;                }

static inline int        Cec_ObjNext( Cec_ManCsw_t * p, int Id )               { return p->pObjs[Id].iNext;               }
static inline void       Cec_ObjSetNext( Cec_ManCsw_t * p, int Id, int Num )   { p->pObjs[Id].iNext = Num;                }

static inline unsigned   Cec_ObjSim( Cec_ManCsw_t * p, int Id )                { return p->pObjs[Id].SimNum;              }
static inline unsigned * Cec_ObjSimP1( Cec_ManCsw_t * p, int Id )              { return &p->pObjs[Id].SimNum;             }
static inline unsigned * Cec_ObjSimP( Cec_ManCsw_t * p, int Id )               { return p->pMems + Cec_ObjSim(p, Id) + 1; }
static inline void       Cec_ObjSetSim( Cec_ManCsw_t * p, int Id, unsigned n ) { p->pObjs[Id].SimNum = n;                 }

static inline int        Cec_ObjIsConst( Cec_ManCsw_t * p, int Id )            { return Cec_ObjRepr(p, Id) == 0;                           }
static inline int        Cec_ObjIsHead( Cec_ManCsw_t * p, int Id )             { return Cec_ObjRepr(p, Id) < 0 && Cec_ObjNext(p, Id) > 0;  }
static inline int        Cec_ObjIsNone( Cec_ManCsw_t * p, int Id )             { return Cec_ObjRepr(p, Id) < 0 && Cec_ObjNext(p, Id) == 0; }
static inline int        Cec_ObjIsTail( Cec_ManCsw_t * p, int Id )             { return Cec_ObjRepr(p, Id) > 0 && Cec_ObjNext(p, Id) == 0; }
static inline int        Cec_ObjIsClass( Cec_ManCsw_t * p, int Id )            { return Cec_ObjRepr(p, Id) > 0 || Cec_ObjNext(p, Id) > 0;  }

#define Cec_ManForEachObj( p, i )                              \
    for ( i = 0; i < Gia_ManObjNum(p->pAig); i++ )
#define Cec_ManForEachObj1( p, i )                             \
    for ( i = 1; i < Gia_ManObjNum(p->pAig); i++ )
#define Cec_ManForEachClass( p, i )                            \
    for ( i = 1; i < Gia_ManObjNum(p->pAig); i++ ) if ( !Cec_ObjIsHead(p, i) ) {} else
#define Cec_ClassForEachObj( p, i, iObj )                      \
    for ( assert(Cec_ObjIsHead(p, i)), iObj = i; iObj; iObj = Cec_ObjNext(p, iObj) )
#define Cec_ClassForEachObj1( p, i, iObj )                     \
    for ( assert(Cec_ObjIsHead(p, i)), iObj = Cec_ObjNext(p, i); iObj; iObj = Cec_ObjNext(p, iObj) )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates the set of representatives.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int * Cec_ManCswDeriveReprs( Cec_ManCsw_t * p )
{
    int i, * pReprs = ABC_FALLOC( int, Gia_ManObjNum(p->pAig) );
    for ( i = 1; i < Gia_ManObjNum(p->pAig); i++ )
        if ( Cec_ObjProved(p, i) )
        {
            assert( Cec_ObjRepr(p, i) >= 0 );
            pReprs[i] = Cec_ObjRepr(p, i);
        }
    return pReprs;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Cec_ManCswDupWithClasses( Cec_ManCsw_t * p )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj, * pRepr;
    int iRes0, iRes1, iRepr, iNode;
    int i, fCompl, * piCopies;
    Vec_IntClear( p->vXorNodes );
    Gia_ManLevelNum( p->pAig );
    pNew = Gia_ManStart( Gia_ManObjNum(p->pAig) );
    pNew->pName = Aig_UtilStrsav( p->pAig->pName );
    Gia_ManHashAlloc( pNew );
    piCopies = ABC_FALLOC( int, Gia_ManObjNum(p->pAig) );
    piCopies[0] = 0;
    Gia_ManForEachObj1( p->pAig, pObj, i )
    {
        if ( Gia_ObjIsCi(pObj) ) 
        {
            piCopies[i] = Gia_ManAppendCi( pNew );
            continue;
        }
        iRes0 = Gia_LitNotCond( piCopies[Gia_ObjFaninId0(pObj,i)], Gia_ObjFaninC0(pObj) );
        if ( Gia_ObjIsCo(pObj) ) 
        {
            Gia_ManAppendCo( pNew, iRes0 );
            continue;
        }
        iRes1 = Gia_LitNotCond( piCopies[Gia_ObjFaninId1(pObj,i)], Gia_ObjFaninC1(pObj) );
        iNode = piCopies[i] = Gia_ManHashAnd( pNew, iRes0, iRes1 );
        if ( Cec_ObjRepr(p, i) < 0 || !Cec_ObjProved(p, i) )
            continue;
        assert( Cec_ObjRepr(p, i) < i );
        iRepr = piCopies[Cec_ObjRepr(p, i)];
        if ( Gia_LitRegular(iNode) == Gia_LitRegular(iRepr) )
            continue;
        pRepr = Gia_ManObj( p->pAig, Cec_ObjRepr(p, i) );
        fCompl = Gia_ObjPhaseReal(pObj) ^ Gia_ObjPhaseReal(pRepr);
        piCopies[i] = Gia_LitNotCond( iRepr, fCompl );
    }
    ABC_FREE( piCopies );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, 0 );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Cec_ManCswSpecReduction( Cec_ManCsw_t * p )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj, * pRepr;
    int iRes0, iRes1, iRepr, iNode, iMiter;
    int i, fCompl, * piCopies, * pDepths;
    Vec_IntClear( p->vXorNodes );
//    Gia_ManLevelNum( p->pAig );
    pNew = Gia_ManStart( Gia_ManObjNum(p->pAig) );
    pNew->pName = Aig_UtilStrsav( p->pAig->pName );
    Gia_ManHashAlloc( pNew );
    piCopies = ABC_FALLOC( int, Gia_ManObjNum(p->pAig) );
    pDepths  = ABC_CALLOC( int, Gia_ManObjNum(p->pAig) );
    piCopies[0] = 0;
    Gia_ManForEachObj1( p->pAig, pObj, i )
    {
        if ( Gia_ObjIsCi(pObj) ) 
        {
            piCopies[i] = Gia_ManAppendCi( pNew );
            continue;
        }
        if ( Gia_ObjIsCo(pObj) ) 
            continue;
        if ( piCopies[Gia_ObjFaninId0(pObj,i)] == -1 ||
             piCopies[Gia_ObjFaninId1(pObj,i)] == -1 )
             continue;
        iRes0 = Gia_LitNotCond( piCopies[Gia_ObjFaninId0(pObj,i)], Gia_ObjFaninC0(pObj) );
        iRes1 = Gia_LitNotCond( piCopies[Gia_ObjFaninId1(pObj,i)], Gia_ObjFaninC1(pObj) );
        iNode = piCopies[i] = Gia_ManHashAnd( pNew, iRes0, iRes1 );
        pDepths[i] = AIG_MAX( pDepths[Gia_ObjFaninId0(pObj,i)], pDepths[Gia_ObjFaninId1(pObj,i)] );
        if ( Cec_ObjRepr(p, i) < 0 || Cec_ObjFailed(p, i) )
            continue;
        assert( Cec_ObjRepr(p, i) < i );
        iRepr = piCopies[Cec_ObjRepr(p, i)];
        if ( iRepr == -1 )
            continue;
        if ( Gia_LitRegular(iNode) == Gia_LitRegular(iRepr) )
            continue;
        pRepr = Gia_ManObj( p->pAig, Cec_ObjRepr(p, i) );
        fCompl = Gia_ObjPhaseReal(pObj) ^ Gia_ObjPhaseReal(pRepr);
        piCopies[i] = Gia_LitNotCond( iRepr, fCompl );
        if ( Cec_ObjProved(p, i) )
            continue;
//        if ( p->pPars->nLevelMax && 
//            (Gia_ObjLevel(p->pAig, pObj)  > p->pPars->nLevelMax || 
//             Gia_ObjLevel(p->pAig, pRepr) > p->pPars->nLevelMax) )
//            continue;
        // produce speculative miter
        iMiter = Gia_ManHashXor( pNew, iNode, piCopies[i] );
        Gia_ManAppendCo( pNew, iMiter );
        Vec_IntPush( p->vXorNodes, Cec_ObjRepr(p, i) );
        Vec_IntPush( p->vXorNodes, i );
        // add to the depth of this node
        pDepths[i] = 1 + AIG_MAX( pDepths[i], pDepths[Cec_ObjRepr(p, i)] );
        if ( p->pPars->nDepthMax && pDepths[i] >= p->pPars->nDepthMax )
            piCopies[i] = -1;
    }
    ABC_FREE( piCopies );
    ABC_FREE( pDepths );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, 0 );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []
 
***********************************************************************/
Gia_Man_t * Cec_ManCswSpecReductionProved( Cec_ManCsw_t * p )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj, * pRepr;
    int iRes0, iRes1, iRepr, iNode, iMiter;
    int i, fCompl, * piCopies;
    Vec_IntClear( p->vXorNodes );
    Gia_ManLevelNum( p->pAig );
    pNew = Gia_ManStart( Gia_ManObjNum(p->pAig) );
    pNew->pName = Aig_UtilStrsav( p->pAig->pName );
    Gia_ManHashAlloc( pNew );
    piCopies = ABC_FALLOC( int, Gia_ManObjNum(p->pAig) );
    piCopies[0] = 0;
    Gia_ManForEachObj1( p->pAig, pObj, i )
    {
        if ( Gia_ObjIsCi(pObj) ) 
        {
            piCopies[i] = Gia_ManAppendCi( pNew );
            continue;
        }
        if ( Gia_ObjIsCo(pObj) ) 
            continue;
        iRes0 = Gia_LitNotCond( piCopies[Gia_ObjFaninId0(pObj,i)], Gia_ObjFaninC0(pObj) );
        iRes1 = Gia_LitNotCond( piCopies[Gia_ObjFaninId1(pObj,i)], Gia_ObjFaninC1(pObj) );
        iNode = piCopies[i] = Gia_ManHashAnd( pNew, iRes0, iRes1 );
        if ( Cec_ObjRepr(p, i) < 0 || !Cec_ObjProved(p, i) )
            continue;
        assert( Cec_ObjRepr(p, i) < i );
        iRepr = piCopies[Cec_ObjRepr(p, i)];
        if ( Gia_LitRegular(iNode) == Gia_LitRegular(iRepr) )
            continue;
        pRepr = Gia_ManObj( p->pAig, Cec_ObjRepr(p, i) );
        fCompl = Gia_ObjPhaseReal(pObj) ^ Gia_ObjPhaseReal(pRepr);
        piCopies[i] = Gia_LitNotCond( iRepr, fCompl );
        // add speculative miter
        iMiter = Gia_ManHashXor( pNew, iNode, piCopies[i] );
        Gia_ManAppendCo( pNew, iMiter );
    }
    ABC_FREE( piCopies );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, 0 );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManCswCountOne( Cec_ManCsw_t * p, int i )
{
    int Ent, nLits = 1;
    Cec_ClassForEachObj1( p, i, Ent )
    {
        assert( Cec_ObjRepr(p, Ent) == i );
        nLits++;
    }
    return nLits;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManCswCountLitsAll( Cec_ManCsw_t * p )
{
    int i, nLits = 0;
    Cec_ManForEachObj( p, i )
        nLits += (Cec_ObjRepr(p, i) >= 0);
    return nLits;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManCswPrintOne( Cec_ManCsw_t * p, int i, int Counter )
{
    int Ent;
    printf( "Class %4d :  Num = %2d  {", Counter, Cec_ManCswCountOne(p, i) );
    Cec_ClassForEachObj( p, i, Ent )
        printf(" %d", Ent );
    printf( " }\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManCswPrintClasses( Cec_ManCsw_t * p, int fVerbose )
{
    int i, Counter = 0, Counter1 = 0, CounterX = 0, nLits;
    Cec_ManForEachObj1( p, i )
    {
        if ( Cec_ObjIsHead(p, i) )
            Counter++;
        else if ( Cec_ObjIsConst(p, i) )
            Counter1++;
        else if ( Cec_ObjIsNone(p, i) )
            CounterX++;
    }
    nLits = Cec_ManCswCountLitsAll( p );
    printf( "Class =%7d. Const =%7d. Unsed =%7d. Lits =%8d. All =%8d. Mem = %5.2f Mb\n", 
        Counter, Counter1, CounterX, nLits-Counter1, nLits, 1.0*p->nMemsMax*(p->pPars->nWords+1)/(1<<20) );
    if ( fVerbose )
    {
        Counter = 0;
        Cec_ManForEachClass( p, i )
            Cec_ManCswPrintOne( p, i, ++Counter );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManCswCompareEqual( unsigned * p0, unsigned * p1, int nWords )
{
    int w;
    if ( (p0[0] & 1) == (p1[0] & 1) )
    {
        for ( w = 0; w < nWords; w++ )
            if ( p0[w] != p1[w] )
                return 0;
        return 1;
    }
    else
    {
        for ( w = 0; w < nWords; w++ )
            if ( p0[w] != ~p1[w] )
                return 0;
        return 1;
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManCswCompareConst( unsigned * p, int nWords )
{
    int w;
    if ( p[0] & 1 )
    {
        for ( w = 0; w < nWords; w++ )
            if ( p[w] != ~0 )
                return 0;
        return 1;
    }
    else
    {
        for ( w = 0; w < nWords; w++ )
            if ( p[w] != 0 )
                return 0;
        return 1;
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManCswClassCreate( Cec_ManCsw_t * p, Vec_Int_t * vClass )
{
    int Repr = -1, EntPrev = -1, Ent, i;
    assert( Vec_IntSize(vClass) > 0 );
    Vec_IntForEachEntry( vClass, Ent, i )
    {
        if ( i == 0 )
        {
            Repr = Ent;
            Cec_ObjSetRepr( p, Ent, -1 );
            EntPrev = Ent;
        }
        else
        {
            Cec_ObjSetRepr( p, Ent, Repr );
            Cec_ObjSetNext( p, EntPrev, Ent );
            EntPrev = Ent;
        }
    }
    Cec_ObjSetNext( p, EntPrev, 0 );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManCswClassRefineOne( Cec_ManCsw_t * p, int i, int fFirst )
{
    unsigned * pSim0, * pSim1;
    int Ent;
    Vec_IntClear( p->vClassOld );
    Vec_IntClear( p->vClassNew );
    Vec_IntPush( p->vClassOld, i );
    pSim0 = fFirst? Cec_ObjSimP1(p, i) : Cec_ObjSimP(p, i);
    Cec_ClassForEachObj1( p, i, Ent )
    {
        pSim1 = fFirst? Cec_ObjSimP1(p, Ent) : Cec_ObjSimP(p, Ent);
        if ( Cec_ManCswCompareEqual( pSim0, pSim1, p->nWords ) )
            Vec_IntPush( p->vClassOld, Ent );
        else
            Vec_IntPush( p->vClassNew, Ent );
    }
    if ( Vec_IntSize( p->vClassNew ) == 0 )
        return 0;
    Cec_ManCswClassCreate( p, p->vClassOld );
    Cec_ManCswClassCreate( p, p->vClassNew );
    if ( Vec_IntSize(p->vClassNew) > 1 )
        return 1 + Cec_ManCswClassRefineOne( p, Vec_IntEntry(p->vClassNew,0), fFirst );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManCswHashKey( unsigned * pSim, int nWords, int nTableSize )
{
    static int s_Primes[16] = { 
        1291, 1699, 1999, 2357, 2953, 3313, 3907, 4177, 
        4831, 5147, 5647, 6343, 6899, 7103, 7873, 8147 };
    unsigned uHash = 0;
    int i;
    if ( pSim[0] & 1 )
        for ( i = 0; i < nWords; i++ )
            uHash ^= ~pSim[i] * s_Primes[i & 0xf];
    else
        for ( i = 0; i < nWords; i++ )
            uHash ^= pSim[i] * s_Primes[i & 0xf];
    return (int)(uHash % nTableSize);

}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManCswClassesCreate( Cec_ManCsw_t * p )
{
    int * pTable, nTableSize, i, Key;
    p->nWords = 1;
    nTableSize = Aig_PrimeCudd( 100 + Gia_ManObjNum(p->pAig) / 10 );
    pTable = ABC_CALLOC( int, nTableSize );
    Cec_ObjSetRepr( p, 0, -1 );
    Cec_ManForEachObj1( p, i )
    {
        if ( Gia_ObjIsCo(Gia_ManObj(p->pAig, i)) ) 
        {
            Cec_ObjSetRepr( p, i, -1 );
            continue;
        }
        if ( Cec_ManCswCompareConst( Cec_ObjSimP1(p, i), p->nWords ) )
        {
            Cec_ObjSetRepr( p, i, 0 );
            continue;
        }
        Key = Cec_ManCswHashKey( Cec_ObjSimP1(p, i), p->nWords, nTableSize );
        if ( pTable[Key] == 0 )
            Cec_ObjSetRepr( p, i, -1 );
        else
        {
            Cec_ObjSetNext( p, pTable[Key], i );
            Cec_ObjSetRepr( p, i, Cec_ObjRepr(p, pTable[Key]) );
            if ( Cec_ObjRepr(p, i) == -1 )
                Cec_ObjSetRepr( p, i, pTable[Key] );
        }
        pTable[Key] = i;
    }
    ABC_FREE( pTable );
    if ( p->pPars->fVeryVerbose )
    Cec_ManCswPrintClasses( p, 0 );
    // refine classes
    Cec_ManForEachClass( p, i )
        Cec_ManCswClassRefineOne( p, i, 1 );
    // clean memory
    Cec_ManForEachObj( p, i )
        Cec_ObjSetSim( p, i, 0 );
    if ( p->pPars->fVeryVerbose )
    Cec_ManCswPrintClasses( p, 0 );
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManCswSimulateSimple( Cec_ManCsw_t * p )
{
    Gia_Obj_t * pObj;
    unsigned Res0, Res1;
    int i;
    Gia_ManForEachCi( p->pAig, pObj, i )
        Cec_ObjSetSim( p, i, Aig_ManRandom(0) );
    Gia_ManForEachAnd( p->pAig, pObj, i )
    {
        Res0 = Cec_ObjSim( p, Gia_ObjFaninId0(pObj, i) );
        Res1 = Cec_ObjSim( p, Gia_ObjFaninId1(pObj, i) );
        Cec_ObjSetSim( p, i, (Gia_ObjFaninC0(pObj)? ~Res0: Res0) &
                             (Gia_ObjFaninC1(pObj)? ~Res1: Res1) );
    }
}

/**Function*************************************************************

  Synopsis    [References simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManCswSimMemRelink( Cec_ManCsw_t * p )
{
    unsigned * pPlace, Ent;
    pPlace = &p->MemFree;
    for ( Ent = p->nMems * (p->nWords + 1); 
          Ent + p->nWords + 1 < (unsigned)p->nWordsAlloc; 
          Ent += p->nWords + 1 )
    {
        *pPlace = Ent;
        pPlace = p->pMems + Ent;
    }
    *pPlace = 0;
}

/**Function*************************************************************

  Synopsis    [References simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Cec_ManCswSimRef( Cec_ManCsw_t * p, int i )
{
    unsigned * pSim;
    assert( p->pObjs[i].SimNum == 0 );
    if ( p->MemFree == 0 )
    {
        if ( p->nWordsAlloc == 0 )
        {
            assert( p->pMems == NULL );
            p->nWordsAlloc = (1<<17); // -> 1Mb
            p->nMems = 1;
        }
        p->nWordsAlloc *= 2;
        p->pMems = ABC_REALLOC( unsigned, p->pMems, p->nWordsAlloc );
        Cec_ManCswSimMemRelink( p );
    }
    p->pObjs[i].SimNum = p->MemFree;
    pSim = p->pMems + p->MemFree;
    p->MemFree = pSim[0];
    pSim[0] = Gia_ObjValue( Gia_ManObj(p->pAig, i) );
    p->nMems++;
    if ( p->nMemsMax < p->nMems )
        p->nMemsMax = p->nMems;
    return pSim;
}

/**Function*************************************************************

  Synopsis    [Dereference simulaton info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned * Cec_ManCswSimDeref( Cec_ManCsw_t * p, int i )
{
    unsigned * pSim;
    assert( p->pObjs[i].SimNum > 0 );
    pSim = p->pMems + p->pObjs[i].SimNum;
    if ( --pSim[0] == 0 )
    {
        pSim[0] = p->MemFree;
        p->MemFree = p->pObjs[i].SimNum;
        p->pObjs[i].SimNum = 0;
        p->nMems--;
    }
    return pSim;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManCswProcessRefined( Cec_ManCsw_t * p, Vec_Int_t * vRefined )
{
    unsigned * pSim;
    int * pTable, nTableSize, i, k, Key;
    if ( Vec_IntSize(vRefined) == 0 )
        return;
    nTableSize = Aig_PrimeCudd( 100 + Vec_IntSize(vRefined) / 5 );
    pTable = ABC_CALLOC( int, nTableSize );
    Vec_IntForEachEntry( vRefined, i, k )
    {
        if ( i == 7720 )
        {
            int s = 0;
        }
        pSim = Cec_ObjSimP( p, i );
        assert( !Cec_ManCswCompareConst( pSim, p->nWords ) );
        Key = Cec_ManCswHashKey( pSim, p->nWords, nTableSize );
        if ( pTable[Key] == 0 )
        {
            assert( Cec_ObjRepr(p, i) == 0 );
            assert( Cec_ObjNext(p, i) == 0 );
            Cec_ObjSetRepr( p, i, -1 );
        }
        else
        {
            Cec_ObjSetNext( p, pTable[Key], i );
            Cec_ObjSetRepr( p, i, Cec_ObjRepr(p, pTable[Key]) );
            if ( Cec_ObjRepr(p, i) == -1 )
                Cec_ObjSetRepr( p, i, pTable[Key] );
            assert( Cec_ObjRepr(p, i) > 0 );
        }
        pTable[Key] = i;
    }
    Vec_IntForEachEntry( vRefined, i, k )
    {
        if ( Cec_ObjIsHead( p, i ) )
            Cec_ManCswClassRefineOne( p, i, 0 );
    }
    Vec_IntForEachEntry( vRefined, i, k )
        Cec_ManCswSimDeref( p, i );
    ABC_FREE( pTable );
}


/**Function*************************************************************

  Synopsis    [Simulates one round.]

  Description [Returns the number of PO entry if failed; 0 otherwise.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ManCswSimulateRound( Cec_ManCsw_t * p, Vec_Ptr_t * vInfoCis, Vec_Ptr_t * vInfoCos, int iSeries, int fRandomize )
{
    static int nCountRand = 0;
    Gia_Obj_t * pObj;
    unsigned * pRes0, * pRes1, * pRes;
    int i, k, w, Ent, iCiId = 0, iCoId = 0;
    p->nMemsMax = 0;
    Vec_IntClear( p->vRefinedC );
    if ( Gia_ObjValue(Gia_ManConst0(p->pAig)) )
    {
        pRes = Cec_ManCswSimRef( p, 0 );
        for ( w = 1; w <= p->nWords; w++ )
            pRes[w] = 0;
    }
    Gia_ManForEachObj1( p->pAig, pObj, i )
    {
        if ( Gia_ObjIsCi(pObj) ) 
        {
            if ( Gia_ObjValue(pObj) == 0 )
            {
                iCiId++;
                continue;
            }
            pRes = Cec_ManCswSimRef( p, i );
            if ( vInfoCis ) 
            {
                pRes0 = Vec_PtrEntry( vInfoCis, iCiId++ );
                for ( w = 1; w <= p->nWords; w++ )
                {
                    pRes[w] = pRes0[iSeries*p->nWords+w-1];
                    if ( fRandomize )
                        pRes[w] ^= (1 << (nCountRand++ & 0x1f));
                }
            }
            else
            {
                for ( w = 1; w <= p->nWords; w++ )
                    pRes[w] = Aig_ManRandom( 0 );
            }
            // make sure the first pattern is always zero
            pRes[1] ^= (pRes[1] & 1);
            goto references;
        }
        if ( Gia_ObjIsCo(pObj) ) // co always has non-zero 1st fanin and zero 2nd fanin
        {
            pRes0 = Cec_ManCswSimDeref( p, Gia_ObjFaninId0(pObj,i) );
            if ( vInfoCos )
            {
                pRes = Vec_PtrEntry( vInfoCos, iCoId++ );
                if ( Gia_ObjFaninC0(pObj) )
                    for ( w = 1; w <= p->nWords; w++ )
                        pRes[w-1] = ~pRes0[w];
                else 
                    for ( w = 1; w <= p->nWords; w++ )
                        pRes[w-1] = pRes0[w];
            }
            continue;
        }
        assert( Gia_ObjValue(pObj) );
        pRes  = Cec_ManCswSimRef( p, i );
        pRes0 = Cec_ManCswSimDeref( p, Gia_ObjFaninId0(pObj,i) );
        pRes1 = Cec_ManCswSimDeref( p, Gia_ObjFaninId1(pObj,i) );
        if ( Gia_ObjFaninC0(pObj) )
        {
            if ( Gia_ObjFaninC1(pObj) )
                for ( w = 1; w <= p->nWords; w++ )
                    pRes[w] = ~(pRes0[w] | pRes1[w]);
            else
                for ( w = 1; w <= p->nWords; w++ )
                    pRes[w] = ~pRes0[w] & pRes1[w];
        }
        else
        {
            if ( Gia_ObjFaninC1(pObj) )
                for ( w = 1; w <= p->nWords; w++ )
                    pRes[w] = pRes0[w] & ~pRes1[w];
            else
                for ( w = 1; w <= p->nWords; w++ )
                    pRes[w] = pRes0[w] & pRes1[w];
        }
references:
        // if this node is candidate constant, collect it
        if ( Cec_ObjIsConst(p, i) && !Cec_ManCswCompareConst(pRes + 1, p->nWords) )
        {
            pRes[0]++;
            Vec_IntPush( p->vRefinedC, i );
        }
        // if the node belongs to a class, save it
        if ( Cec_ObjIsClass(p, i) )
            pRes[0]++;
        // if this is the last node of the class, process it
        if ( Cec_ObjIsTail(p, i) )
        {
            Vec_IntClear( p->vClassTemp );
            Cec_ClassForEachObj( p, Cec_ObjRepr(p, i), Ent )
                Vec_IntPush( p->vClassTemp, Ent );
            Cec_ManCswClassRefineOne( p, Cec_ObjRepr(p, i), 0 );
            Vec_IntForEachEntry( p->vClassTemp, Ent, k )
                Cec_ManCswSimDeref( p, Ent );
        }
    }
    if ( Vec_IntSize(p->vRefinedC) > 0 )
        Cec_ManCswProcessRefined( p, p->vRefinedC );
    assert( vInfoCis == NULL || iCiId == Gia_ManCiNum(p->pAig) );
    assert( vInfoCos == NULL || iCoId == Gia_ManCoNum(p->pAig) );
    assert( p->nMems == 1 );
    if ( p->pPars->fVeryVerbose )
        Cec_ManCswPrintClasses( p, 0 );
/*
    if ( p->nMems > 1 )
    {
        for ( i = 1; i < p->nObjs; i++ )
        if ( p->pSims[i] )
        {
            int x = 0;
        }
    }
*/
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManCswClassesPrepare( Cec_ManCsw_t * p )
{
    int i;
    Gia_ManSetRefs( p->pAig );
    Cec_ManCswSimulateSimple( p );
    Cec_ManCswClassesCreate( p );
    for ( i = 0; i < p->pPars->nRounds; i++ )
    {
        p->nWords = i + 1;
        Cec_ManCswSimMemRelink( p );
        Cec_ManCswSimulateRound( p, NULL, NULL, 0, 0 );
    }
    p->nWords = p->pPars->nWords;
    Cec_ManCswSimMemRelink( p );
    for ( i = 0; i < p->pPars->nRounds; i++ )
        Cec_ManCswSimulateRound( p, NULL, NULL, 0, 0 );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManCswClassesUpdate_rec( Gia_Obj_t * pObj )
{
    int Result;
    if ( pObj->fMark0 )
        return 1;
    if ( Gia_ObjIsCi(pObj) || Gia_ObjIsConst0(pObj) )
        return 0;
    Result = (Cec_ManCswClassesUpdate_rec( Gia_ObjFanin0(pObj) ) |
              Cec_ManCswClassesUpdate_rec( Gia_ObjFanin1(pObj) ));
    return pObj->fMark0 = Result;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cec_ManCswClassesUpdate( Cec_ManCsw_t * p, Cec_ManPat_t * pPat, Gia_Man_t * pNew )
{
    Vec_Ptr_t * vInfo;
    Gia_Obj_t * pObj, * pObjOld, * pReprOld;
    int i, k, iRepr, iNode;
    vInfo = Cec_ManPatCollectPatterns( pPat, Gia_ManCiNum(p->pAig), p->pPars->nWords );
    if ( vInfo != NULL )
    {
        for ( i = 0; i < pPat->nSeries; i++ )
            Cec_ManCswSimulateRound( p, vInfo, NULL, i, 0 );
        Vec_PtrFree( vInfo );
    }
    assert( Vec_IntSize(p->vXorNodes) == 2*Gia_ManCoNum(pNew) );
    // mark the transitive fanout of failed nodes
    if ( p->pPars->nDepthMax != 1 )
    {
        Gia_ManCleanMark0( p->pAig );
        Gia_ManCleanMark1( p->pAig );
        Gia_ManForEachCo( pNew, pObj, k )
        {
            iRepr = Vec_IntEntry( p->vXorNodes, 2*k );
            iNode = Vec_IntEntry( p->vXorNodes, 2*k+1 );
            if ( pObj->fMark0 == 0 && pObj->fMark1 == 1 ) // proved
                continue;
//            Gia_ManObj(p->pAig, iRepr)->fMark0 = 1;
            Gia_ManObj(p->pAig, iNode)->fMark0 = 1;
        }
        // mark the nodes reachable through the failed nodes
        Gia_ManForEachAnd( p->pAig, pObjOld, k )
            pObjOld->fMark0 |= (Gia_ObjFanin0(pObjOld)->fMark0 | Gia_ObjFanin1(pObjOld)->fMark0);
        // unmark the disproved nodes
        Gia_ManForEachCo( pNew, pObj, k )
        {
            iRepr = Vec_IntEntry( p->vXorNodes, 2*k );
            iNode = Vec_IntEntry( p->vXorNodes, 2*k+1 );
            if ( pObj->fMark0 == 0 && pObj->fMark1 == 1 ) // proved
                continue; 
            pObjOld = Gia_ManObj(p->pAig, iNode);
            assert( pObjOld->fMark0 == 1 );
            if ( Gia_ObjFanin0(pObjOld)->fMark0 == 0 && Gia_ObjFanin1(pObjOld)->fMark0 == 0 )
                pObjOld->fMark1 = 1;
        }
        // clean marks
        Gia_ManForEachAnd( p->pAig, pObjOld, k )
            if ( pObjOld->fMark1 )
            {
                pObjOld->fMark0 = 0;
                pObjOld->fMark1 = 0;
            }
    }
    // set the results
    Gia_ManForEachCo( pNew, pObj, k )
    {
        iRepr = Vec_IntEntry( p->vXorNodes, 2*k );
        iNode = Vec_IntEntry( p->vXorNodes, 2*k+1 );
        pReprOld = Gia_ManObj(p->pAig, iRepr);
        pObjOld = Gia_ManObj(p->pAig, iNode);
        if ( pObj->fMark1 )
        { // proved
            assert( pObj->fMark0 == 0 );
            assert( !Cec_ObjProved(p, iNode) );
            if ( pReprOld->fMark0 == 0 && pObjOld->fMark0 == 0 )
//            if ( pObjOld->fMark0 == 0 )
            {
                assert( iRepr == Cec_ObjRepr(p, iNode) );
                Cec_ObjSetProved( p, iNode );
                p->nAllProved++;
            }
        }
        else if ( pObj->fMark0 )
        { // disproved
            assert( pObj->fMark1 == 0 );
            if ( pReprOld->fMark0 == 0 && pObjOld->fMark0 == 0 )
//            if ( pObjOld->fMark0 == 0 )
            {
                if ( iRepr == Cec_ObjRepr(p, iNode) )
                    printf( "Cec_ManCswClassesUpdate(): Error! Node is not refined!\n" );
                p->nAllDisproved++;
            }
        }
        else
        { // failed
            assert( pObj->fMark0 == 0 );
            assert( pObj->fMark1 == 0 );
            assert( !Cec_ObjFailed(p, iNode) );
            assert( !Cec_ObjProved(p, iNode) );
            Cec_ObjSetFailed( p, iNode );
            p->nAllFailed++;
        }
    } 
    return 0;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


