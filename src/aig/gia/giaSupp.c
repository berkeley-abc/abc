/**CFile****************************************************************

  FileName    [giaSupp.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Support minimization for AIGs.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaSupp.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

#ifdef ABC_USE_CUDD
#include "bdd/extrab/extraBdd.h"
#endif

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#ifdef ABC_USE_CUDD

struct Gia_ManMin_t_ 
{
    // problem formulation
    Gia_Man_t *     pGia;
    int             iLits[2];
    // structural information
    Vec_Int_t *     vCis[2];
    Vec_Int_t *     vObjs[2];
    Vec_Int_t *     vCleared;  
    // intermediate functions
    DdManager *     dd;
    Vec_Ptr_t *     vFuncs;
    Vec_Int_t *     vSupp;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Create/delete the data representation manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_ManMin_t * Gia_ManSuppStart( Gia_Man_t * pGia )
{
    Gia_ManMin_t * p;
    p = ABC_CALLOC( Gia_ManMin_t, 1 );
    p->pGia     = pGia;
    p->vCis[0]  = Vec_IntAlloc( 512 );
    p->vCis[1]  = Vec_IntAlloc( 512 );
    p->vObjs[0] = Vec_IntAlloc( 512 );
    p->vObjs[1] = Vec_IntAlloc( 512 );
    p->vCleared = Vec_IntAlloc( 512 );
    p->dd = Cudd_Init( 0, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
//    Cudd_AutodynEnable( p->dd,  CUDD_REORDER_SYMM_SIFT );
    Cudd_AutodynDisable( p->dd );
    p->vFuncs   = Vec_PtrAlloc( 10000 );
    p->vSupp    = Vec_IntAlloc( 10000 );
    return p;
}
void Gia_ManSuppStop( Gia_ManMin_t * p )
{
    Vec_IntFreeP( &p->vCis[0] );
    Vec_IntFreeP( &p->vCis[1] );
    Vec_IntFreeP( &p->vObjs[0] );
    Vec_IntFreeP( &p->vObjs[1] );
    Vec_IntFreeP( &p->vCleared );
    Vec_PtrFreeP( &p->vFuncs );
    Vec_IntFreeP( &p->vSupp );
    printf( "Refs = %d. \n", Cudd_CheckZeroRef( p->dd ) );
    Cudd_Quit( p->dd );
    ABC_FREE( p );
}

/**Function*************************************************************

  Synopsis    [Compute variables, which are not in the support.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManFindRemoved( Gia_ManMin_t * p ) 
{
    extern void ddSupportStep2( DdNode * f, int * support );
    extern void ddClearFlag2( DdNode * f );

    //int fVerbose = 1;
    int nBddLimit = 100000;
    int nPart0 = Vec_IntSize(p->vCis[0]);
    int n, i, iObj, nVars = 0;
    DdNode * bFunc0, * bFunc1, * bFunc;
    Vec_PtrFillExtra( p->vFuncs, Gia_ManObjNum(p->pGia), NULL );
    // assign variables
    for ( n = 0; n < 2; n++ )
        Vec_IntForEachEntry( p->vCis[n], iObj, i )
            Vec_PtrWriteEntry( p->vFuncs, iObj, Cudd_bddIthVar(p->dd, nVars++) );
    // create nodes
    for ( n = 0; n < 2; n++ )
        Vec_IntForEachEntry( p->vObjs[n], iObj, i )
        {
            Gia_Obj_t * pObj = Gia_ManObj( p->pGia, iObj );
            bFunc0 = Cudd_NotCond( (DdNode *)Vec_PtrEntry(p->vFuncs, Gia_ObjFaninId0(pObj, iObj)), Gia_ObjFaninC0(pObj) );
            bFunc1 = Cudd_NotCond( (DdNode *)Vec_PtrEntry(p->vFuncs, Gia_ObjFaninId1(pObj, iObj)), Gia_ObjFaninC1(pObj) );
            bFunc  = Cudd_bddAndLimit( p->dd, bFunc0, bFunc1, nBddLimit );  
            assert( bFunc != NULL );
            Cudd_Ref( bFunc );
            Vec_PtrWriteEntry( p->vFuncs, iObj, bFunc );
        }
    // create new node
    bFunc0 = Cudd_NotCond( (DdNode *)Vec_PtrEntry(p->vFuncs, Abc_Lit2Var(p->iLits[0])), Abc_LitIsCompl(p->iLits[0]) );
    bFunc1 = Cudd_NotCond( (DdNode *)Vec_PtrEntry(p->vFuncs, Abc_Lit2Var(p->iLits[1])), Abc_LitIsCompl(p->iLits[1]) );
    bFunc  = Cudd_bddAndLimit( p->dd, bFunc0, bFunc1, nBddLimit );  
    assert( bFunc != NULL );
    Cudd_Ref( bFunc );
    //if ( fVerbose ) Extra_bddPrint( p->dd, bFunc ), printf( "\n" );
    // collect support
    Vec_IntFill( p->vSupp, nVars, 0 );
    ddSupportStep2( Cudd_Regular(bFunc), Vec_IntArray(p->vSupp) );
    ddClearFlag2( Cudd_Regular(bFunc) );
    // find variables not present in the support
    Vec_IntClear( p->vCleared );
    for ( i = 0; i < nVars; i++ )
        if ( Vec_IntEntry(p->vSupp, i) == 0 )
            Vec_IntPush( p->vCleared, i < nPart0 ? Vec_IntEntry(p->vCis[0], i) : Vec_IntEntry(p->vCis[1], i-nPart0) );
    //printf( "%d(%d)%d  ", Cudd_SupportSize(p->dd, bFunc), Vec_IntSize(p->vCleared), Cudd_DagSize(bFunc) );
    // deref results
    Cudd_RecursiveDeref( p->dd, bFunc );
    for ( n = 0; n < 2; n++ )
        Vec_IntForEachEntry( p->vObjs[n], iObj, i )
            Cudd_RecursiveDeref( p->dd, (DdNode *)Vec_PtrEntry(p->vFuncs, iObj) );
    //Vec_IntPrint( p->vCleared );
    return Vec_IntSize(p->vCleared);
}

/**Function*************************************************************

  Synopsis    [Compute variables, which are not in the support.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManRebuildOne( Gia_ManMin_t * p, int n ) 
{
    int i, iObj, iGiaLitNew = -1;
    Vec_Int_t * vTempIns = p->vCis[n]; 
    Vec_Int_t * vTempNds = p->vObjs[n];
    Vec_Int_t * vCopies  = &p->pGia->vCopies;
    Vec_IntFillExtra( vCopies, Gia_ManObjNum(p->pGia), -1 );
    assert( p->iLits[n] >= 2 );
    // process inputs
    Vec_IntForEachEntry( vTempIns, iObj, i )
        Vec_IntWriteEntry( vCopies, iObj, Abc_Var2Lit(iObj, 0) );
    // process constants
    assert( Vec_IntSize(p->vCleared) > 0 );
    Vec_IntForEachEntry( p->vCleared, iObj, i )
        Vec_IntWriteEntry( vCopies, iObj, 0 );
    if ( Vec_IntSize(vTempNds) == 0 )
        iGiaLitNew = Vec_IntEntry( vCopies, Abc_Lit2Var(p->iLits[n]) );
    else
    {
        Vec_IntForEachEntry( vTempNds, iObj, i )
        {
            Gia_Obj_t * pObj = Gia_ManObj( p->pGia, iObj );
            int iGiaLit0 = Vec_IntEntry( vCopies, Gia_ObjFaninId0p(p->pGia, pObj) );
            int iGiaLit1 = Vec_IntEntry( vCopies, Gia_ObjFaninId1p(p->pGia, pObj) );
            iGiaLit0   = Abc_LitNotCond( iGiaLit0, Gia_ObjFaninC0(pObj) );
            iGiaLit1   = Abc_LitNotCond( iGiaLit1, Gia_ObjFaninC1(pObj) );
            iGiaLitNew = Gia_ManHashAnd( p->pGia, iGiaLit0, iGiaLit1 );
            Vec_IntWriteEntry( vCopies, iObj, iGiaLitNew );
        }
        assert( Abc_Lit2Var(p->iLits[n]) == iObj );
    }
    return Abc_LitNotCond( iGiaLitNew, Abc_LitIsCompl(p->iLits[n]) );
}

/**Function*************************************************************

  Synopsis    [Collect nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Gia_ManGatherSupp_rec( Gia_Man_t * p, int iObj, Vec_Int_t * vCis, Vec_Int_t * vObjs )
{
    int Val0, Val1;
    Gia_Obj_t * pObj;
    if ( Gia_ObjIsTravIdPreviousId(p, iObj) )
        return 1;
    if ( Gia_ObjIsTravIdCurrentId(p, iObj) )
        return 0;
    Gia_ObjSetTravIdCurrentId(p, iObj);
    pObj = Gia_ManObj( p, iObj );
    if ( Gia_ObjIsCi(pObj) )
    {
        Vec_IntPush( vCis, iObj );
        return 0;
    }
    assert( Gia_ObjIsAnd(pObj) );
    Val0 = Gia_ManGatherSupp_rec( p, Gia_ObjFaninId0(pObj, iObj), vCis, vObjs );
    Val1 = Gia_ManGatherSupp_rec( p, Gia_ObjFaninId1(pObj, iObj), vCis, vObjs );
    Vec_IntPush( vObjs, iObj );
    return Val0 || Val1;
}
int Gia_ManGatherSupp( Gia_ManMin_t * p )
{
    int n, Overlap = 0;
    Gia_ManIncrementTravId( p->pGia );
    for ( n = 0; n < 2; n++ )
    {
        Vec_IntClear( p->vCis[n] );
        Vec_IntClear( p->vObjs[n] );
        Gia_ManIncrementTravId( p->pGia );
        Overlap = Gia_ManGatherSupp_rec( p->pGia, Abc_Lit2Var(p->iLits[n]), p->vCis[n], p->vObjs[n] );
        assert( n || !Overlap );
    }
    return Overlap;
}

/**Function*************************************************************

  Synopsis    [Takes a literal and returns a support-minized literal.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_ManSupportAnd( Gia_ManMin_t * p, int iLit0, int iLit1 )
{
    int iLitNew0, iLitNew1;
    p->iLits[0] = iLit0;
    p->iLits[1] = iLit1;
    if ( iLit0 < 2 || iLit1 < 2 || !Gia_ManGatherSupp(p) || !Gia_ManFindRemoved(p) )
        return Gia_ManHashAnd( p->pGia, iLit0, iLit1 );
    iLitNew0 = Gia_ManRebuildOne( p, 0 );
    iLitNew1 = Gia_ManRebuildOne( p, 1 );
    return Gia_ManHashAnd( p->pGia, iLitNew0, iLitNew1 );
}


#else

Gia_ManMin_t * Gia_ManSuppStart( Gia_Man_t * pGia )              { return NULL; }
int Gia_ManSupportAnd( Gia_ManMin_t * p, int iLit0, int iLit1 )  { return 0;    }
void Gia_ManSuppStop( Gia_ManMin_t * p )                         {}

#endif


/**Function*************************************************************

  Synopsis    [Testbench.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_ManSupportAndTest( Gia_Man_t * pGia )
{
    Gia_ManMin_t * pMan;
    Gia_Man_t * pNew, * pTemp;
    Gia_Obj_t * pObj;
    int i;
    Gia_ManFillValue( pGia );
    pNew = Gia_ManStart( Gia_ManObjNum(pGia) );
    pNew->pName = Abc_UtilStrsav( pGia->pName );
    pNew->pSpec = Abc_UtilStrsav( pGia->pSpec );
    Gia_ManHashAlloc( pNew );
    Gia_ManConst0(pGia)->Value = 0;
    pMan = Gia_ManSuppStart( pNew );
    Gia_ManForEachObj1( pGia, pObj, i )
    {
        if ( Gia_ObjIsAnd(pObj) )
        {
//            pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
            pObj->Value = Gia_ManSupportAnd( pMan, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
        }
        else if ( Gia_ObjIsCi(pObj) )
            pObj->Value = Gia_ManAppendCi( pNew );
        else if ( Gia_ObjIsCo(pObj) )
            pObj->Value = Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
        else assert( 0 );

        if ( i % 10000 == 0 )
            printf( "%d\n", i );
    }
    Gia_ManSuppStop( pMan );
    Gia_ManSetRegNum( pNew, Gia_ManRegNum(pGia) );
    pNew = Gia_ManCleanup( pTemp = pNew );
    Gia_ManStop( pTemp );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

