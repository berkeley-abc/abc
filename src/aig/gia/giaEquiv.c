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
    assert( p->pReprs );
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
    assert( Gia_ManEquivCheckLits( p, nLits ) );
    if ( fVerbose )
    {
        printf( "Const0 = " );
        Gia_ManForEachConst( p, i )
            printf( "%d ", i );
        printf( "\n" );
        Counter = 0;
        Gia_ManForEachClass( p, i )
            Gia_ManEquivPrintOne( p, i, ++Counter );
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
        printf( "Speculatively reduced model has no primary outputs.\n" );
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

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


