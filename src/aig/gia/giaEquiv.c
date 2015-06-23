/**CFile****************************************************************

  FileName    [giaEquiv.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Manipulation of equivalence classes.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaEquiv.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns 1 if AIG is not in the required topo order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManCheckTopoOrder_rec( Gia_Man_t * p, Gia_Obj_t * pObj )
{
    Gia_Obj_t * pRepr;
    if ( pObj->Value == 0 )
        return 1;
    pObj->Value = 0;
    assert( Gia_ObjIsAnd(pObj) );
    if ( !Gia_ManCheckTopoOrder_rec( p, Gia_ObjFanin0(pObj) ) )
        return 0;
    if ( !Gia_ManCheckTopoOrder_rec( p, Gia_ObjFanin1(pObj) ) )
        return 0;
    pRepr = Gia_ObjReprObj( p, Gia_ObjId(p,pObj) );
    return pRepr == NULL || pRepr->Value == 0;
}

/**Function*************************************************************

  Synopsis    [Returns 0 if AIG is not in the required topo order.]

  Description [AIG should be in such an order that the representative
  is always traversed before the node.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManCheckTopoOrder( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, RetValue = 1;
    Gia_ManFillValue( p );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = 0;
    Gia_ManForEachCo( p, pObj, i )
        RetValue &= Gia_ManCheckTopoOrder_rec( p, Gia_ObjFanin0(pObj) );
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Given representatives, derives pointers to the next objects.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int * Gia_ManDeriveNexts( Gia_Man_t * p )
{
    unsigned * pNexts, * pTails;
    int i;
    assert( p->pReprs != NULL );
    assert( p->pNexts == NULL );
    pNexts = ABC_CALLOC( unsigned, Gia_ManObjNum(p) );
    pTails = ABC_ALLOC( unsigned, Gia_ManObjNum(p) );
    for ( i = 0; i < Gia_ManObjNum(p); i++ )
        pTails[i] = i;
    for ( i = 0; i < Gia_ManObjNum(p); i++ )
    {
        if ( !p->pReprs[i].iRepr || p->pReprs[i].iRepr == GIA_VOID )
            continue;
        pNexts[ pTails[p->pReprs[i].iRepr] ] = i;
        pTails[p->pReprs[i].iRepr] = i;
    }
    ABC_FREE( pTails );
    return (int *)pNexts;
}

/**Function*************************************************************

  Synopsis    [Given points to the next objects, derives representatives.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManDeriveReprs( Gia_Man_t * p )
{
    int i, iObj;
    assert( p->pReprs == NULL );
    assert( p->pNexts != NULL );
    p->pReprs = ABC_CALLOC( Gia_Rpr_t, Gia_ManObjNum(p) );
    for ( i = 0; i < Gia_ManObjNum(p); i++ )
        Gia_ObjSetRepr( p, i, GIA_VOID );
    for ( i = 0; i < Gia_ManObjNum(p); i++ )
    {
        if ( p->pNexts[i] == 0 )
            continue;
        if ( p->pReprs[i].iRepr != GIA_VOID )
            continue;
        // next is set, repr is not set
        for ( iObj = p->pNexts[i]; iObj; iObj = p->pNexts[iObj] )
            p->pReprs[iObj].iRepr = i;
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManEquivCountOne( Gia_Man_t * p, int i )
{
    int Ent, nLits = 1;
    Gia_ClassForEachObj1( p, i, Ent )
    {
        assert( Gia_ObjRepr(p, Ent) == i );
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
void Gia_ManEquivPrintOne( Gia_Man_t * p, int i, int Counter )
{
    int Ent;
    printf( "Class %4d :  Num = %2d  {", Counter, Gia_ManEquivCountOne(p, i) );
    Gia_ClassForEachObj( p, i, Ent )
    {
        printf(" %d", Ent );
        if ( p->pReprs[Ent].fColorA || p->pReprs[Ent].fColorB )
            printf(" <%d%d>", p->pReprs[Ent].fColorA, p->pReprs[Ent].fColorB );
    }
    printf( " }\n" );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManEquivCountLitsAll( Gia_Man_t * p )
{
    int i, nLits = 0;
    for ( i = 0; i < Gia_ManObjNum(p); i++ )
        nLits += (Gia_ObjRepr(p, i) != GIA_VOID);
    return nLits;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManEquivCountClasses( Gia_Man_t * p )
{
    int i, Counter = 0;
    for ( i = 1; i < Gia_ManObjNum(p); i++ )
        Counter += Gia_ObjIsHead(p, i);
    return Counter;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManEquivCheckLits( Gia_Man_t * p, int nLits )
{
    int nLitsReal = Gia_ManEquivCountLitsAll( p );
    if ( nLitsReal != nLits )
        printf( "Detected a mismatch in counting equivalence classes (%d).\n", nLitsReal - nLits );
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManPrintStatsClasses( Gia_Man_t * p )
{
    int i, Counter = 0, Counter0 = 0, CounterX = 0, Proved = 0, nLits;
    for ( i = 1; i < Gia_ManObjNum(p); i++ )
    {
        if ( Gia_ObjIsHead(p, i) )
            Counter++;
        else if ( Gia_ObjIsConst(p, i) )
            Counter0++;
        else if ( Gia_ObjIsNone(p, i) )
            CounterX++;
        if ( Gia_ObjProved(p, i) )
            Proved++;
    }
    CounterX -= Gia_ManCoNum(p);
    nLits = Gia_ManCiNum(p) + Gia_ManAndNum(p) - Counter - CounterX;

//    printf( "i/o/ff =%5d/%5d/%5d  ", Gia_ManPiNum(p), Gia_ManPoNum(p), Gia_ManRegNum(p) );
//    printf( "and =%5d  ", Gia_ManAndNum(p) );
//    printf( "lev =%3d  ", Gia_ManLevelNum(p) );
    printf( "cst =%3d  cls =%6d  lit =%8d\n", Counter0, Counter, nLits );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManEquivCountLits( Gia_Man_t * p )
{
    int i, Counter = 0, Counter0 = 0, CounterX = 0;
    if ( p->pReprs == NULL || p->pNexts == NULL )
        return 0;
    for ( i = 1; i < Gia_ManObjNum(p); i++ )
    {
        if ( Gia_ObjIsHead(p, i) )
            Counter++;
        else if ( Gia_ObjIsConst(p, i) )
            Counter0++;
        else if ( Gia_ObjIsNone(p, i) )
            CounterX++;
    }
    CounterX -= Gia_ManCoNum(p);
    return Gia_ManCiNum(p) + Gia_ManAndNum(p) - Counter - CounterX;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManEquivPrintClasses( Gia_Man_t * p, int fVerbose, float Mem )
{
    int i, Counter = 0, Counter0 = 0, CounterX = 0, Proved = 0, nLits;
    for ( i = 1; i < Gia_ManObjNum(p); i++ )
    {
        if ( Gia_ObjIsHead(p, i) )
            Counter++;
        else if ( Gia_ObjIsConst(p, i) )
            Counter0++;
        else if ( Gia_ObjIsNone(p, i) )
            CounterX++;
        if ( Gia_ObjProved(p, i) )
            Proved++;
    }
    CounterX -= Gia_ManCoNum(p);
    nLits = Gia_ManCiNum(p) + Gia_ManAndNum(p) - Counter - CounterX;
    printf( "cst =%8d  cls =%7d  lit =%8d  unused =%8d  proof =%6d  mem =%5.2f Mb\n", 
        Counter0, Counter, nLits, CounterX, Proved, (Mem == 0.0) ? 8.0*Gia_ManObjNum(p)/(1<<20) : Mem );
//    printf( "cst =%8d  cls =%7d  lit =%8d\n", 
//        Counter0, Counter, nLits );
    assert( Gia_ManEquivCheckLits( p, nLits ) );
    if ( fVerbose )
    {
        int Ent;
/*
        printf( "Const0 = " );
        Gia_ManForEachConst( p, i )
            printf( "%d ", i );
        printf( "\n" );
        Counter = 0;
        Gia_ManForEachClass( p, i )
            Gia_ManEquivPrintOne( p, i, ++Counter );
*/
        Gia_ManLevelNum( p );
        Gia_ManForEachClass( p, i )
            if ( i % 100 == 0 )
            {
//                printf( "%d ", Gia_ManEquivCountOne(p, i) );
                Gia_ClassForEachObj( p, i, Ent )
                {
                    printf( "%d ", Gia_ObjLevel( p, Gia_ManObj(p, Ent) ) );
                }
                printf( "\n" );
            }
    }
}

/**Function*************************************************************

  Synopsis    [Returns representative node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Gia_Obj_t * Gia_ManEquivRepr( Gia_Man_t * p, Gia_Obj_t * pObj, int fUseAll, int fDualOut )
{
    if ( fUseAll )
    {
        if ( Gia_ObjRepr(p, Gia_ObjId(p,pObj)) == GIA_VOID )
            return NULL;
    } 
    else
    {
        if ( !Gia_ObjProved(p, Gia_ObjId(p,pObj)) )
            return NULL;
    }
//    if ( fDualOut && !Gia_ObjDiffColors( p, Gia_ObjId(p, pObj), Gia_ObjRepr(p, Gia_ObjId(p,pObj)) ) )
    if ( fDualOut && !Gia_ObjDiffColors2( p, Gia_ObjId(p, pObj), Gia_ObjRepr(p, Gia_ObjId(p,pObj)) ) )
        return NULL;
    return Gia_ManObj( p, Gia_ObjRepr(p, Gia_ObjId(p,pObj)) );
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManEquivReduce_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj, int fUseAll, int fDualOut )
{
    Gia_Obj_t * pRepr;
    if ( (pRepr = Gia_ManEquivRepr(p, pObj, fUseAll, fDualOut)) )
    {
        Gia_ManEquivReduce_rec( pNew, p, pRepr, fUseAll, fDualOut );
        pObj->Value = Gia_LitNotCond( pRepr->Value, Gia_ObjPhaseReal(pRepr) ^ Gia_ObjPhaseReal(pObj) );
        return;
    }
    if ( ~pObj->Value )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    Gia_ManEquivReduce_rec( pNew, p, Gia_ObjFanin0(pObj), fUseAll, fDualOut );
    Gia_ManEquivReduce_rec( pNew, p, Gia_ObjFanin1(pObj), fUseAll, fDualOut );
    pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
}

/**Function*************************************************************

  Synopsis    [Reduces AIG using equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManEquivReduce( Gia_Man_t * p, int fUseAll, int fDualOut, int fVerbose )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;
    if ( !p->pReprs )
    {
        printf( "Gia_ManEquivReduce(): Equivalence classes are not available.\n" );
        return NULL;
    }
    if ( fDualOut && (Gia_ManPoNum(p) & 1) )
    {
        printf( "Gia_ManEquivReduce(): Dual-output miter should have even number of POs.\n" );
        return NULL;
    }
    // check if there are any equivalences defined
    Gia_ManForEachObj( p, pObj, i )
        if ( Gia_ObjReprObj(p, i) != NULL )
            break;
    if ( i == Gia_ManObjNum(p) )
    {
        printf( "Gia_ManEquivReduce(): There are no equivalences to reduce.\n" );
        return NULL;
    }
/*
    if ( !Gia_ManCheckTopoOrder( p ) )
    {
        printf( "Gia_ManEquivReduce(): AIG is not in a correct topological order.\n" );
        return NULL;
    }
*/
    Gia_ManSetPhase( p );
    if ( fDualOut )
        Gia_ManEquivSetColors( p, fVerbose );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Gia_UtilStrsav( p->pName );
    Gia_ManFillValue( p );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManHashAlloc( pNew );
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManEquivReduce_rec( pNew, p, Gia_ObjFanin0(pObj), fUseAll, fDualOut );
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Reduces AIG using equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManEquivFixOutputPairs( Gia_Man_t * p )
{
    Gia_Obj_t * pObj0, * pObj1;
    int i;
    assert( (Gia_ManPoNum(p) & 1) == 0 ); 
    Gia_ManForEachPo( p, pObj0, i )
    {
        pObj1 = Gia_ManPo( p, ++i );
        if ( Gia_ObjChild0(pObj0) != Gia_ObjChild0(pObj1) )
            continue;
        pObj0->iDiff0  = Gia_ObjId(p, pObj0);
        pObj0->fCompl0 = 0;
        pObj1->iDiff0  = Gia_ObjId(p, pObj1);
        pObj1->fCompl0 = 0;
    }
}

/**Function*************************************************************

  Synopsis    [Removes pointers to the unmarked nodes..]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManEquivUpdatePointers( Gia_Man_t * p, Gia_Man_t * pNew )
{
    Gia_Obj_t * pObj, * pObjNew;
    int i;
    Gia_ManForEachObj( p, pObj, i )
    {
        if ( !~pObj->Value )
            continue;
        pObjNew = Gia_ManObj( pNew, Gia_Lit2Var(pObj->Value) );
        if ( pObjNew->fMark0 )
            pObj->Value = ~0;
    }
}

/**Function*************************************************************

  Synopsis    [Removes pointers to the unmarked nodes..]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManEquivDeriveReprs( Gia_Man_t * p, Gia_Man_t * pNew, Gia_Man_t * pFinal )
{
    Vec_Int_t * vClass;
    Gia_Obj_t * pObj, * pObjNew;
    int i, k, iNode, iRepr, iPrev;
    // start representatives
    pFinal->pReprs = ABC_CALLOC( Gia_Rpr_t, Gia_ManObjNum(pFinal) );
    for ( i = 0; i < Gia_ManObjNum(pFinal); i++ )
        Gia_ObjSetRepr( pFinal, i, GIA_VOID );
    // iterate over constant candidates
    Gia_ManForEachConst( p, i )
    {
        pObj = Gia_ManObj( p, i );
        if ( !~pObj->Value )
            continue;
        pObjNew = Gia_ManObj( pNew, Gia_Lit2Var(pObj->Value) );
        if ( Gia_Lit2Var(pObjNew->Value) == 0 )
            continue;
        Gia_ObjSetRepr( pFinal, Gia_Lit2Var(pObjNew->Value), 0 );
    }
    // iterate over class candidates
    vClass = Vec_IntAlloc( 100 );
    Gia_ManForEachClass( p, i )
    {
        Vec_IntClear( vClass );
        Gia_ClassForEachObj( p, i, k )
        {
            pObj = Gia_ManObj( p, k );
            if ( !~pObj->Value )
                continue;
            pObjNew = Gia_ManObj( pNew, Gia_Lit2Var(pObj->Value) );
            Vec_IntPushUnique( vClass, Gia_Lit2Var(pObjNew->Value) );
        }
        if ( Vec_IntSize( vClass ) < 2 )
            continue;
        Vec_IntSort( vClass, 0 );
        iRepr = iPrev = Vec_IntEntry( vClass, 0 );
        Vec_IntForEachEntryStart( vClass, iNode, k, 1 )
        {
            Gia_ObjSetRepr( pFinal, iNode, iRepr );
            assert( iPrev < iNode );
            iPrev = iNode;
        }
    }
    Vec_IntFree( vClass );
    pFinal->pNexts = Gia_ManDeriveNexts( pFinal );
}

/**Function*************************************************************

  Synopsis    [Removes pointers to the unmarked nodes..]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManEquivRemapDfs( Gia_Man_t * p )
{
    Gia_Man_t * pNew;
    Vec_Int_t * vClass;
    int i, k, iNode, iRepr, iPrev;
    pNew = Gia_ManDupDfs( p );
    // start representatives
    pNew->pReprs = ABC_CALLOC( Gia_Rpr_t, Gia_ManObjNum(pNew) );
    for ( i = 0; i < Gia_ManObjNum(pNew); i++ )
        Gia_ObjSetRepr( pNew, i, GIA_VOID );
    // iterate over constant candidates
    Gia_ManForEachConst( p, i )
        Gia_ObjSetRepr( pNew, Gia_Lit2Var(Gia_ManObj(p, i)->Value), 0 );
    // iterate over class candidates
    vClass = Vec_IntAlloc( 100 );
    Gia_ManForEachClass( p, i )
    {
        Vec_IntClear( vClass );
        Gia_ClassForEachObj( p, i, k )
            Vec_IntPushUnique( vClass, Gia_Lit2Var(Gia_ManObj(p, k)->Value) );
        assert( Vec_IntSize( vClass ) > 1 );
        Vec_IntSort( vClass, 0 );
        iRepr = iPrev = Vec_IntEntry( vClass, 0 );
        Vec_IntForEachEntryStart( vClass, iNode, k, 1 )
        {
            Gia_ObjSetRepr( pNew, iNode, iRepr );
            assert( iPrev < iNode );
            iPrev = iNode;
        }
    }
    Vec_IntFree( vClass );
    pNew->pNexts = Gia_ManDeriveNexts( pNew );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Reduces AIG while remapping equivalence classes.]

  Description [Drops the pairs of outputs if they are proved equivalent.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManEquivReduceAndRemap( Gia_Man_t * p, int fSeq, int fMiterPairs )
{
    Gia_Man_t * pNew, * pFinal;
    pNew = Gia_ManEquivReduce( p, 0, 0, 0 );
    if ( pNew == NULL )
        return NULL;
    if ( fMiterPairs )
        Gia_ManEquivFixOutputPairs( pNew );
    if ( fSeq )
        Gia_ManSeqMarkUsed( pNew );
    else
        Gia_ManCombMarkUsed( pNew );
    Gia_ManEquivUpdatePointers( p, pNew );
    pFinal = Gia_ManDupMarked( pNew );
    Gia_ManEquivDeriveReprs( p, pNew, pFinal );
    Gia_ManStop( pNew );
    pFinal = Gia_ManEquivRemapDfs( pNew = pFinal );
    Gia_ManStop( pNew );
    return pFinal;
}

/**Function*************************************************************

  Synopsis    [Marks CIs/COs/ANDs unreachable from POs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManEquivSetColor_rec( Gia_Man_t * p, Gia_Obj_t * pObj, int fOdds )
{
    if ( Gia_ObjVisitColor( p, Gia_ObjId(p,pObj), fOdds ) )
        return 0;
    if ( Gia_ObjIsRo(p, pObj) )
        return 1 + Gia_ManEquivSetColor_rec( p, Gia_ObjFanin0(Gia_ObjRoToRi(p, pObj)), fOdds );
    assert( Gia_ObjIsAnd(pObj) );
    return 1 + Gia_ManEquivSetColor_rec( p, Gia_ObjFanin0(pObj), fOdds )
             + Gia_ManEquivSetColor_rec( p, Gia_ObjFanin1(pObj), fOdds );
}

/**Function*************************************************************

  Synopsis    [Marks CIs/COs/ANDs unreachable from POs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManEquivSetColors( Gia_Man_t * p, int fVerbose )
{
    Gia_Obj_t * pObj;
    int i, nNodes[2], nDiffs[2];
    assert( (Gia_ManPoNum(p) & 1) == 0 );
    Gia_ObjSetColors( p, 0 );
    Gia_ManForEachPi( p, pObj, i )
        Gia_ObjSetColors( p, Gia_ObjId(p,pObj) );
    nNodes[0] = nNodes[1] = Gia_ManPiNum(p);
    Gia_ManForEachPo( p, pObj, i )
        nNodes[i&1] += Gia_ManEquivSetColor_rec( p, Gia_ObjFanin0(pObj), i&1 );
//    Gia_ManForEachObj( p, pObj, i )
//        if ( Gia_ObjIsCi(pObj) || Gia_ObjIsAnd(pObj) )
//            assert( Gia_ObjColors(p, i) );
    nDiffs[0] = Gia_ManCandNum(p) - nNodes[0];
    nDiffs[1] = Gia_ManCandNum(p) - nNodes[1];
    if ( fVerbose )
    {
        printf( "CI+AND = %7d  A = %7d  B = %7d  Ad = %7d  Bd = %7d  AB = %7d.\n", 
            Gia_ManCandNum(p), nNodes[0], nNodes[1], nDiffs[0], nDiffs[1], 
            Gia_ManCandNum(p) - nDiffs[0] - nDiffs[1] );
    }
    return (nDiffs[0] + nDiffs[1]) / 2;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Gia_ManSpecBuild( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vXorLits, int fDualOut )
{
    Gia_Obj_t * pRepr;
    unsigned iLitNew;
    pRepr = Gia_ObjReprObj( p, Gia_ObjId(p,pObj) );
    if ( pRepr == NULL )
        return;
//    if ( fDualOut && !Gia_ObjDiffColors( p, Gia_ObjId(p, pObj), Gia_ObjId(p, pRepr) ) )
    if ( fDualOut && !Gia_ObjDiffColors2( p, Gia_ObjId(p, pObj), Gia_ObjId(p, pRepr) ) )
        return;
    iLitNew = Gia_LitNotCond( pRepr->Value, Gia_ObjPhaseReal(pRepr) ^ Gia_ObjPhaseReal(pObj) );
    if ( pObj->Value != iLitNew && !Gia_ObjProved(p, Gia_ObjId(p,pObj)) )
        Vec_IntPush( vXorLits, Gia_ManHashXor(pNew, pObj->Value, iLitNew) );
    pObj->Value = iLitNew;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if AIG has dangling nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManHasNoEquivs( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i;
    if ( p->pReprs == NULL )
        return 1;
    Gia_ManForEachObj( p, pObj, i )
        if ( Gia_ObjReprObj(p, i) != NULL )
            break;
    return i == Gia_ManObjNum(p);
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManSpecReduce_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vXorLits, int fDualOut )
{
    if ( ~pObj->Value )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    Gia_ManSpecReduce_rec( pNew, p, Gia_ObjFanin0(pObj), vXorLits, fDualOut );
    Gia_ManSpecReduce_rec( pNew, p, Gia_ObjFanin1(pObj), vXorLits, fDualOut );
    pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManSpecBuild( pNew, p, pObj, vXorLits, fDualOut );
}

/**Function*************************************************************

  Synopsis    [Reduces AIG using equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManSpecReduce( Gia_Man_t * p, int fDualOut, int fVerbose )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    Vec_Int_t * vXorLits;
    int i, iLitNew;
    if ( !p->pReprs )
    {
        printf( "Gia_ManSpecReduce(): Equivalence classes are not available.\n" );
        return NULL;
    }
    if ( fDualOut && (Gia_ManPoNum(p) & 1) )
    {
        printf( "Gia_ManSpecReduce(): Dual-output miter should have even number of POs.\n" );
        return NULL;
    }
    if ( Gia_ManHasNoEquivs(p) )
    {
        printf( "Gia_ManSpecReduce(): There are no equivalences to reduce.\n" );
        return NULL;
    }
/*
    if ( !Gia_ManCheckTopoOrder( p ) )
    {
        printf( "Gia_ManSpecReduce(): AIG is not in a correct topological order.\n" );
        return NULL;
    }
*/
    vXorLits = Vec_IntAlloc( 1000 );
    Gia_ManSetPhase( p );
    Gia_ManFillValue( p );
    if ( fDualOut )
        Gia_ManEquivSetColors( p, fVerbose );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Gia_UtilStrsav( p->pName );
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManForEachRo( p, pObj, i )
        Gia_ManSpecBuild( pNew, p, pObj, vXorLits, fDualOut );
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManSpecReduce_rec( pNew, p, Gia_ObjFanin0(pObj), vXorLits, fDualOut );
    Vec_IntForEachEntry( vXorLits, iLitNew, i )
        Gia_ManAppendCo( pNew, iLitNew );
    if ( Vec_IntSize(vXorLits) == 0 )
    {
        printf( "Speculatively reduced model has no primary outputs.\n" );
        Gia_ManAppendCo( pNew, 0 );
    }
    Gia_ManForEachRi( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManHashStop( pNew );
    Vec_IntFree( vXorLits );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManSpecBuildInit( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vXorLits, int f, int fDualOut )
{
    Gia_Obj_t * pRepr;
    int iLitNew;
    pRepr = Gia_ObjReprObj( p, Gia_ObjId(p,pObj) );
    if ( pRepr == NULL )
        return;
//    if ( fDualOut && !Gia_ObjDiffColors( p, Gia_ObjId(p, pObj), Gia_ObjId(p, pRepr) ) )
    if ( fDualOut && !Gia_ObjDiffColors2( p, Gia_ObjId(p, pObj), Gia_ObjId(p, pRepr) ) )
        return;
    iLitNew = Gia_LitNotCond( Gia_ObjCopyF(p, f, pRepr), Gia_ObjPhaseReal(pRepr) ^ Gia_ObjPhaseReal(pObj) );
    if ( Gia_ObjCopyF(p, f, pObj) != iLitNew && !Gia_ObjProved(p, Gia_ObjId(p,pObj)) )
        Vec_IntPush( vXorLits, Gia_ManHashXor(pNew, Gia_ObjCopyF(p, f, pObj), iLitNew) );
    Gia_ObjSetCopyF( p, f, pObj, iLitNew );
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManSpecReduceInit_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj, Vec_Int_t * vXorLits, int f, int fDualOut )
{
    if ( ~Gia_ObjCopyF(p, f, pObj) )
        return;
    assert( Gia_ObjIsAnd(pObj) );
    Gia_ManSpecReduceInit_rec( pNew, p, Gia_ObjFanin0(pObj), vXorLits, f, fDualOut );
    Gia_ManSpecReduceInit_rec( pNew, p, Gia_ObjFanin1(pObj), vXorLits, f, fDualOut );
    Gia_ObjSetCopyF( p, f, pObj, Gia_ManHashAnd(pNew, Gia_ObjFanin0CopyF(p, f, pObj), Gia_ObjFanin1CopyF(p, f, pObj)) );
    Gia_ManSpecBuildInit( pNew, p, pObj, vXorLits, f, fDualOut );
}

/**Function*************************************************************

  Synopsis    [Creates initialized SRM with the given number of frames.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManSpecReduceInit( Gia_Man_t * p, Gia_Cex_t * pInit, int nFrames, int fDualOut )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj, * pObjRi, * pObjRo;
    Vec_Int_t * vXorLits;
    int f, i, iLitNew;
    if ( !p->pReprs )
    {
        printf( "Gia_ManSpecReduceInit(): Equivalence classes are not available.\n" );
        return NULL;
    }
    if ( Gia_ManRegNum(p) == 0 )
    {
        printf( "Gia_ManSpecReduceInit(): Circuit is not sequential.\n" );
        return NULL;
    }
    if ( Gia_ManRegNum(p) != pInit->nRegs )
    {
        printf( "Gia_ManSpecReduceInit(): Mismatch in the number of registers.\n" );
        return NULL;
    }
    if ( fDualOut && (Gia_ManPoNum(p) & 1) )
    {
        printf( "Gia_ManSpecReduceInit(): Dual-output miter should have even number of POs.\n" );
        return NULL;
    }

/*
    if ( !Gia_ManCheckTopoOrder( p ) )
    {
        printf( "Gia_ManSpecReduceInit(): AIG is not in a correct topological order.\n" );
        return NULL;
    }
*/
    assert( pInit->nRegs == Gia_ManRegNum(p) && pInit->nPis == 0 );
    p->pCopies = ABC_FALLOC( int, nFrames * Gia_ManObjNum(p) );
    vXorLits = Vec_IntAlloc( 1000 );
    Gia_ManSetPhase( p );
    if ( fDualOut )
        Gia_ManEquivSetColors( p, 0 );
    pNew = Gia_ManStart( nFrames * Gia_ManObjNum(p) );
    pNew->pName = Gia_UtilStrsav( p->pName );
    Gia_ManHashAlloc( pNew );
    Gia_ManForEachRo( p, pObj, i )
        Gia_ObjSetCopyF( p, 0, pObj, Gia_InfoHasBit(pInit->pData, i) );
    for ( f = 0; f < nFrames; f++ )
    {
        Gia_ObjSetCopyF( p, f, Gia_ManConst0(p), 0 );
        Gia_ManForEachPi( p, pObj, i )
            Gia_ObjSetCopyF( p, f, pObj, Gia_ManAppendCi(pNew) );
        Gia_ManForEachRo( p, pObj, i )
            Gia_ManSpecBuildInit( pNew, p, pObj, vXorLits, f, fDualOut );
        Gia_ManForEachCo( p, pObj, i )
        {
            Gia_ManSpecReduceInit_rec( pNew, p, Gia_ObjFanin0(pObj), vXorLits, f, fDualOut );
            Gia_ObjSetCopyF( p, f, pObj, Gia_ObjFanin0CopyF(p, f, pObj) );
        }
        if ( f == nFrames - 1 )
            break;
        Gia_ManForEachRiRo( p, pObjRi, pObjRo, i )
            Gia_ObjSetCopyF( p, f+1, pObjRo, Gia_ObjCopyF(p, f, pObjRi) );
    }
    Vec_IntForEachEntry( vXorLits, iLitNew, i )
        Gia_ManAppendCo( pNew, iLitNew );
    if ( Vec_IntSize(vXorLits) == 0 )
    {
//        printf( "Speculatively reduced model has no primary outputs.\n" );
        Gia_ManAppendCo( pNew, 0 );
    }
    ABC_FREE( p->pCopies );
    Vec_IntFree( vXorLits );
    Gia_ManHashStop( pNew );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Creates initialized SRM with the given number of frames.]

  Description [Uses as many frames as needed to create the number of 
  output not less than the number of equivalence literals.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManSpecReduceInitFrames( Gia_Man_t * p, Gia_Cex_t * pInit, int nFramesMax, int * pnFrames, int fDualOut, int nMinOutputs )
{
    Gia_Man_t * pFrames;
    int f, nLits;
    nLits = Gia_ManEquivCountLits( p );
    for ( f = 1; ; f++ )
    {
        pFrames = Gia_ManSpecReduceInit( p, pInit, f, fDualOut );
        if ( (nMinOutputs == 0 && Gia_ManPoNum(pFrames) >= nLits/2+1) || 
             (nMinOutputs != 0 && Gia_ManPoNum(pFrames) >= nMinOutputs) )
            break;
        if ( f == nFramesMax )
            break;
        Gia_ManStop( pFrames );
        pFrames = NULL;
    }
    if ( f == nFramesMax )
        printf( "Stopped unrolling after %d frames.\n", nFramesMax );
    if ( pnFrames )
        *pnFrames = f;
    return pFrames;
}

/**Function*************************************************************

  Synopsis    [Transforms equiv classes by removing the AB nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManEquivTransform( Gia_Man_t * p, int fVerbose )
{
    extern void Cec_ManSimClassCreate( Gia_Man_t * p, Vec_Int_t * vClass );
    Vec_Int_t * vClass, * vClassNew;
    int iRepr, iNode, Ent, k;
    int nRemovedLits = 0, nRemovedClas = 0;
    int nTotalLits = 0, nTotalClas = 0;
    Gia_Obj_t * pObj;
    int i;
    assert( p->pReprs && p->pNexts );
    vClass = Vec_IntAlloc( 100 );
    vClassNew = Vec_IntAlloc( 100 );
    Gia_ManForEachObj( p, pObj, i )
        if ( Gia_ObjIsCi(pObj) || Gia_ObjIsAnd(pObj) )
            assert( Gia_ObjColors(p, i) );
    Gia_ManForEachClassReverse( p, iRepr )
    {
        nTotalClas++;
        Vec_IntClear( vClass );
        Vec_IntClear( vClassNew );
        Gia_ClassForEachObj( p, iRepr, iNode )
        {
            nTotalLits++;
            Vec_IntPush( vClass, iNode );
            assert( Gia_ObjColors(p, iNode) );
            if ( Gia_ObjColors(p, iNode) != 3 )
                Vec_IntPush( vClassNew, iNode );
            else
                nRemovedLits++;
        }
        Vec_IntForEachEntry( vClass, Ent, k )
        {
            p->pReprs[Ent].fFailed = p->pReprs[Ent].fProved = 0;
            p->pReprs[Ent].iRepr = GIA_VOID;
            p->pNexts[Ent] = 0;
        }
        if ( Vec_IntSize(vClassNew) < 2 )
        {
            nRemovedClas++;
            continue;
        }
        Cec_ManSimClassCreate( p, vClassNew );
    }
    Vec_IntFree( vClass );
    Vec_IntFree( vClassNew );
    if ( fVerbose )
    printf( "Removed classes = %6d (out of %6d). Removed literals = %6d (out of %6d).\n", 
        nRemovedClas, nTotalClas, nRemovedLits, nTotalLits );
}

/**Function*************************************************************

  Synopsis    [Transforms equiv classes by setting a good representative.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManEquivImprove( Gia_Man_t * p )
{
    Vec_Int_t * vClass;
    int i, k, iNode, iRepr;
    int iReprBest, iLevelBest, iLevelCur, iMffcBest, iMffcCur;
    assert( p->pReprs != NULL && p->pNexts != NULL );
    Gia_ManLevelNum( p );
    Gia_ManCreateRefs( p );
    // iterate over class candidates
    vClass = Vec_IntAlloc( 100 );
    Gia_ManForEachClass( p, i )
    {
        Vec_IntClear( vClass );
        iReprBest = -1;
        iLevelBest = iMffcBest = ABC_INFINITY;
        Gia_ClassForEachObj( p, i, k )
        {
            iLevelCur = Gia_ObjLevel( p,Gia_ManObj(p, k) );
            iMffcCur  = Gia_NodeMffcSize( p, Gia_ManObj(p, k) );
            if ( iLevelBest > iLevelCur || (iLevelBest == iLevelCur && iMffcBest > iMffcCur) )
            {
                iReprBest  = k;
                iLevelBest = iLevelCur;
                iMffcBest  = iMffcCur;
            }
            Vec_IntPush( vClass, k );
        }
        assert( Vec_IntSize( vClass ) > 1 );
        assert( iReprBest > 0 );
        if ( i == iReprBest )
            continue;
/*
        printf( "Repr/Best = %6d/%6d. Lev = %3d/%3d. Mffc = %3d/%3d.\n", 
            i, iReprBest, Gia_ObjLevel( p,Gia_ManObj(p, i) ), Gia_ObjLevel( p,Gia_ManObj(p, iReprBest) ),
            Gia_NodeMffcSize( p, Gia_ManObj(p, i) ), Gia_NodeMffcSize( p, Gia_ManObj(p, iReprBest) ) );
*/
        iRepr = iReprBest;
        Gia_ObjSetRepr( p, iRepr, GIA_VOID );
        Gia_ObjSetProved( p, i );
        Gia_ObjUnsetProved( p, iRepr );
        Vec_IntForEachEntry( vClass, iNode, k )
            if ( iNode != iRepr )
                Gia_ObjSetRepr( p, iNode, iRepr );
    }
    Vec_IntFree( vClass );
    ABC_FREE( p->pNexts );
//    p->pNexts = Gia_ManDeriveNexts( p );
}


/**Function*************************************************************

  Synopsis    [Returns 1 if pOld is in the TFI of pNode.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ObjCheckTfi_rec( Gia_Man_t * p, Gia_Obj_t * pOld, Gia_Obj_t * pNode, Vec_Ptr_t * vVisited )
{
    // check the trivial cases
    if ( pNode == NULL )
        return 0;
    if ( Gia_ObjIsCi(pNode) )
        return 0;
//    if ( pNode->Id < pOld->Id ) // cannot use because of choices of pNode
//        return 0;
    if ( pNode == pOld )
        return 1;
    // skip the visited node
    if ( pNode->fMark0 )
        return 0;
    pNode->fMark0 = 1;
    Vec_PtrPush( vVisited, pNode );
    // check the children
    if ( Gia_ObjCheckTfi_rec( p, pOld, Gia_ObjFanin0(pNode), vVisited ) )
        return 1;
    if ( Gia_ObjCheckTfi_rec( p, pOld, Gia_ObjFanin1(pNode), vVisited ) )
        return 1;
    // check equivalent nodes
    return Gia_ObjCheckTfi_rec( p, pOld, Gia_ObjNextObj(p, Gia_ObjId(p, pNode)), vVisited );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if pOld is in the TFI of pNode.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ObjCheckTfi( Gia_Man_t * p, Gia_Obj_t * pOld, Gia_Obj_t * pNode )
{
    Vec_Ptr_t * vVisited;
    Gia_Obj_t * pObj;
    int RetValue, i;
    assert( !Gia_IsComplement(pOld) );
    assert( !Gia_IsComplement(pNode) );
    vVisited = Vec_PtrAlloc( 100 );
    RetValue = Gia_ObjCheckTfi_rec( p, pOld, pNode, vVisited );
    Vec_PtrForEachEntry( vVisited, pObj, i )
        pObj->fMark0 = 0;
    Vec_PtrFree( vVisited );
    return RetValue;
}


/**Function*************************************************************

  Synopsis    [Adds the next entry while making choices.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManAddNextEntry_rec( Gia_Man_t * p, Gia_Obj_t * pOld, Gia_Obj_t * pNode )
{
    if ( Gia_ObjNext(p, Gia_ObjId(p, pOld)) == 0 )
    {
        Gia_ObjSetNext( p, Gia_ObjId(p, pOld), Gia_ObjId(p, pNode) );
        return;
    }
    Gia_ManAddNextEntry_rec( p, Gia_ObjNextObj(p, Gia_ObjId(p, pOld)), pNode );
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManEquivToChoices_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj )
{
    Gia_Obj_t * pRepr, * pReprNew, * pObjNew;
    if ( ~pObj->Value )
        return;
    if ( (pRepr = Gia_ObjReprObj(p, Gia_ObjId(p, pObj))) )
    {
        if ( Gia_ObjIsConst0(pRepr) )
        {
            pObj->Value = Gia_LitNotCond( pRepr->Value, Gia_ObjPhaseReal(pRepr) ^ Gia_ObjPhaseReal(pObj) );
            return;
        }
        Gia_ManEquivToChoices_rec( pNew, p, pRepr );
        assert( Gia_ObjIsAnd(pObj) );
        Gia_ManEquivToChoices_rec( pNew, p, Gia_ObjFanin0(pObj) );
        Gia_ManEquivToChoices_rec( pNew, p, Gia_ObjFanin1(pObj) );
        pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        if ( Gia_LitRegular(pObj->Value) == Gia_LitRegular(pRepr->Value) )
        {
            assert( (int)pObj->Value == Gia_LitNotCond( pRepr->Value, Gia_ObjPhaseReal(pRepr) ^ Gia_ObjPhaseReal(pObj) ) );
            return;
        }
        if ( pRepr->Value > pObj->Value ) // should never happen with high resource limit
            return;
        assert( pRepr->Value < pObj->Value );
        pReprNew = Gia_ManObj( pNew, Gia_Lit2Var(pRepr->Value) );
        pObjNew  = Gia_ManObj( pNew, Gia_Lit2Var(pObj->Value) );
        if ( Gia_ObjReprObj( pNew, Gia_ObjId(pNew, pObjNew) ) )
        {
            assert( Gia_ObjReprObj( pNew, Gia_ObjId(pNew, pObjNew) ) == pReprNew );
            pObj->Value = Gia_LitNotCond( pRepr->Value, Gia_ObjPhaseReal(pRepr) ^ Gia_ObjPhaseReal(pObj) );
            return;
        }
        if ( !Gia_ObjCheckTfi( pNew, pReprNew, pObjNew ) )
        {
            assert( Gia_ObjNext(pNew, Gia_ObjId(pNew, pObjNew)) == 0 );
            Gia_ObjSetRepr( pNew, Gia_ObjId(pNew, pObjNew), Gia_ObjId(pNew, pReprNew) );
            Gia_ManAddNextEntry_rec( pNew, pReprNew, pObjNew ); 
        }
        pObj->Value = Gia_LitNotCond( pRepr->Value, Gia_ObjPhaseReal(pRepr) ^ Gia_ObjPhaseReal(pObj) );
        return;
    }
    assert( Gia_ObjIsAnd(pObj) );
    Gia_ManEquivToChoices_rec( pNew, p, Gia_ObjFanin0(pObj) );
    Gia_ManEquivToChoices_rec( pNew, p, Gia_ObjFanin1(pObj) );
    pObj->Value = Gia_ManHashAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
}

/**Function*************************************************************

  Synopsis    [Removes choices, which contain fanouts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_ManRemoveBadChoices( Gia_Man_t * p )
{
    Gia_Obj_t * pObj;
    int i, iObj, iPrev, Counter = 0;
    // mark nodes with fanout
    Gia_ManForEachObj( p, pObj, i )
    {
        pObj->fMark0 = 0;
        if ( Gia_ObjIsAnd(pObj) )
        {
            Gia_ObjFanin0(pObj)->fMark0 = 1;
            Gia_ObjFanin1(pObj)->fMark0 = 1;
        }
        else if ( Gia_ObjIsCo(pObj) )
            Gia_ObjFanin0(pObj)->fMark0 = 1;
    }
    // go through the classes and remove 
    Gia_ManForEachClass( p, i )
    {
        for ( iPrev = i, iObj = Gia_ObjNext(p, i); iObj; iObj = Gia_ObjNext(p, iPrev) )
        {
            if ( !Gia_ManObj(p, iObj)->fMark0 )
            {
                iPrev = iObj; 
                continue;
            }
            Gia_ObjSetRepr( p, iObj, GIA_VOID );
            Gia_ObjSetNext( p, iPrev, Gia_ObjNext(p, iObj) );
            Gia_ObjSetNext( p, iObj, 0 );
            Counter++;
        } 
    }
    // remove the marks
    Gia_ManCleanMark0( p );
//    printf( "Removed %d bad choices.\n", Counter );
}

/**Function*************************************************************

  Synopsis    [Reduces AIG using equivalence classes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManEquivToChoices( Gia_Man_t * p, int nSnapshots )
{
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj, * pRepr;
    int i;
    assert( (Gia_ManCoNum(p) % nSnapshots) == 0 );
    Gia_ManSetPhase( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Gia_UtilStrsav( p->pName );
    pNew->pReprs = ABC_CALLOC( Gia_Rpr_t, Gia_ManObjNum(p) );
    pNew->pNexts = ABC_CALLOC( int, Gia_ManObjNum(p) );
    for ( i = 0; i < Gia_ManObjNum(p); i++ )
        Gia_ObjSetRepr( pNew, i, GIA_VOID );
    Gia_ManFillValue( p );
    Gia_ManConst0(p)->Value = 0;
    Gia_ManForEachCi( p, pObj, i )
        pObj->Value = Gia_ManAppendCi(pNew);
    Gia_ManForEachRo( p, pObj, i )
        if ( (pRepr = Gia_ObjReprObj(p, Gia_ObjId(p, pObj))) )
        {
            assert( Gia_ObjIsConst0(pRepr) || Gia_ObjIsRo(p, pRepr) );
            pObj->Value = pRepr->Value;
        }
    Gia_ManHashAlloc( pNew );
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManEquivToChoices_rec( pNew, p, Gia_ObjFanin0(pObj) );
    Gia_ManForEachCo( p, pObj, i )
        if ( i % nSnapshots == 0 )
            Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManHashStop( pNew );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(p) );
    Gia_ManRemoveBadChoices( pNew );
//    Gia_ManEquivPrintClasses( pNew, 0, 0 );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
//    Gia_ManEquivPrintClasses( pNew, 0, 0 );
    return pNew;
}

#include "aig.h"
#include "saig.h"
#include "cec.h"
#include "giaAig.h"

/**Function*************************************************************

  Synopsis    [Implements iteration during speculation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_CommandSpecI( Gia_Man_t * pGia, int nFramesInit, int nBTLimitInit, int fStart, int fCheckMiter, int fVerbose )
{
    extern int Cec_ManCheckNonTrivialCands( Gia_Man_t * pAig );
    Aig_Man_t * pTemp;
    Gia_Man_t * pSrm, * pReduce, * pAux;
    int nIter, nStart = 0;
    if ( pGia->pReprs == NULL || pGia->pNexts == NULL )
    {
        printf( "Gia_CommandSpecI(): Equivalence classes are not defined.\n" );
        return 0;
    }
    // (spech)*  where spech = &srm; restore save3; bmc2 -F 100 -C 25000; &resim
    Gia_ManCleanMark0( pGia );
    Gia_ManPrintStats( pGia, 0 );
    for ( nIter = 0; ; nIter++ )
    {
        if ( Gia_ManHasNoEquivs(pGia) )
        {
            printf( "Gia_CommandSpecI: No equivalences left.\n" );
            break;
        }
        printf( "ITER %3d : ", nIter );
//      if ( fVerbose )
//            printf( "Starting BMC from frame %d.\n", nStart );
//      if ( fVerbose )
//            Gia_ManPrintStats( pGia, 0 );
            Gia_ManPrintStatsClasses( pGia );
        // perform speculative reduction
//        if ( Gia_ManPoNum(pSrm) <= Gia_ManPoNum(pGia) )
        if ( !Cec_ManCheckNonTrivialCands(pGia) )
        {
            printf( "Gia_CommandSpecI: There are only trivial equiv candidates left (PO drivers). Quitting.\n" );
            break;
        }
        pSrm = Gia_ManSpecReduce( pGia, 0, 0 ); 
        // bmc2 -F 100 -C 25000
        {
            Gia_Cex_t * pCex;
            int nFrames     = nFramesInit; // different from default
            int nNodeDelta  = 2000;
            int nBTLimit    = nBTLimitInit; // different from default
            int nBTLimitAll = 2000000;
            pTemp = Gia_ManToAig( pSrm, 0 );
//            Aig_ManPrintStats( pTemp );
            Gia_ManStop( pSrm );
            Saig_BmcPerform( pTemp, nStart, nFrames, nNodeDelta, 20, nBTLimit, nBTLimitAll, fVerbose, 0 );
            pCex = pTemp->pSeqModel; pTemp->pSeqModel = NULL;
            Aig_ManStop( pTemp );
            if ( pCex == NULL )
            {
                printf( "Gia_CommandSpecI(): Internal BMC could not find a counter-example.\n" );
                break;
            }
            if ( fStart ) 
                nStart = pCex->iFrame;
            // perform simulation
            {
                Cec_ParSim_t Pars, * pPars = &Pars;
                Cec_ManSimSetDefaultParams( pPars );
                pPars->fCheckMiter = fCheckMiter;
                if ( Cec_ManSeqResimulateCounter( pGia, pPars, pCex ) )
                {
                    ABC_FREE( pCex );
                    break;
                }
                ABC_FREE( pCex );
            }
        } 
        // write equivalence classes
        Gia_WriteAiger( pGia, "gore.aig", 0, 0 );
        // reduce the model
        pReduce = Gia_ManSpecReduce( pGia, 0, 0 );
        if ( pReduce )
        {
            pReduce = Gia_ManSeqStructSweep( pAux = pReduce, 1, 1, 0 );
            Gia_ManStop( pAux );
            Gia_WriteAiger( pReduce, "gsrm.aig", 0, 0 );
//            printf( "Speculatively reduced model was written into file \"%s\".\n", "gsrm.aig" );
//          Gia_ManPrintStatsShort( pReduce );
            Gia_ManStop( pReduce );
        }
    }
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


