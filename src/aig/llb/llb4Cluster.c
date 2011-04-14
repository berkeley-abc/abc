/**CFile****************************************************************

  FileName    [llb2Cluster.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [BDD based reachability.]

  Synopsis    [Non-linear quantification scheduling.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: llb2Cluster.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "llbInt.h"

ABC_NAMESPACE_IMPL_START
 

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline int Llb_MnxBddVar( Vec_Int_t * vOrder, Aig_Obj_t * pObj ) { return Vec_IntEntry(vOrder, Aig_ObjId(pObj)); }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Find good static variable ordering.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_Nonlin4FindOrder_rec( Aig_Man_t * pAig, Aig_Obj_t * pObj, Vec_Int_t * vOrder, int * pCounter )
{
    Aig_Obj_t * pFanin0, * pFanin1;
    if ( Aig_ObjIsTravIdCurrent(pAig, pObj) )
        return;
    Aig_ObjSetTravIdCurrent( pAig, pObj );
    assert( Llb_MnxBddVar(vOrder, pObj) < 0 );
    if ( Aig_ObjIsPi(pObj) )
    {
        Vec_IntWriteEntry( vOrder, Aig_ObjId(pObj), (*pCounter)++ );
        return;
    }
    // try fanins with higher level first
    pFanin0 = Aig_ObjFanin0(pObj);
    pFanin1 = Aig_ObjFanin1(pObj);
//    if ( pFanin0->Level > pFanin1->Level || (pFanin0->Level == pFanin1->Level && pFanin0->Id < pFanin1->Id) )
    if ( pFanin0->Level > pFanin1->Level )
    {
        Llb_Nonlin4FindOrder_rec( pAig, pFanin0, vOrder, pCounter );
        Llb_Nonlin4FindOrder_rec( pAig, pFanin1, vOrder, pCounter );
    }
    else
    {
        Llb_Nonlin4FindOrder_rec( pAig, pFanin1, vOrder, pCounter );
        Llb_Nonlin4FindOrder_rec( pAig, pFanin0, vOrder, pCounter );
    }
    Vec_IntWriteEntry( vOrder, Aig_ObjId(pObj), (*pCounter)++ );
}

/**Function*************************************************************

  Synopsis    [Find good static variable ordering.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Llb_Nonlin4FindOrder( Aig_Man_t * pAig )
{
    Vec_Int_t * vNodes = NULL;
    Vec_Int_t * vOrder;
    Aig_Obj_t * pObj;
    int i, Counter = 0;
    // collect nodes in the order
    vOrder = Vec_IntStartFull( Aig_ManObjNumMax(pAig) );
    Aig_ManIncrementTravId( pAig );
    Aig_ObjSetTravIdCurrent( pAig, Aig_ManConst1(pAig) );
    Aig_ManForEachPo( pAig, pObj, i )
    {
printf( "PO %d Var %d\n", i, Counter );
        Vec_IntWriteEntry( vOrder, Aig_ObjId(pObj), Counter++ );
        Llb_Nonlin4FindOrder_rec( pAig, Aig_ObjFanin0(pObj), vOrder, &Counter );
    }
    Aig_ManForEachPi( pAig, pObj, i )
        if ( Llb_MnxBddVar(vOrder, pObj) < 0 )
            Vec_IntWriteEntry( vOrder, Aig_ObjId(pObj), Counter++ );
    Aig_ManCleanMarkA( pAig );
    Vec_IntFreeP( &vNodes );
    assert( Counter == Aig_ManObjNum(pAig) - 1 );
    return vOrder;
}

/**Function*************************************************************

  Synopsis    [Derives BDDs for the partitions.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Llb_Nonlin4FindPartitions( DdManager * dd, Aig_Man_t * pAig, Vec_Int_t * vOrder )
{
    Vec_Ptr_t * vRoots;
    Aig_Obj_t * pObj;
    DdNode * bBdd, * bBdd0, * bBdd1, * bPart;
    int i;
    Aig_ManCleanData( pAig );
    // assign elementary variables
    Aig_ManConst1(pAig)->pData = Cudd_ReadOne(dd); 
    Aig_ManForEachPi( pAig, pObj, i )
        pObj->pData = Cudd_bddIthVar( dd, Llb_MnxBddVar(vOrder, pObj) );
    Aig_ManForEachNode( pAig, pObj, i )
        if ( Llb_MnxBddVar(vOrder, pObj) >= 0 )
        {
            pObj->pData = Cudd_bddIthVar( dd, Llb_MnxBddVar(vOrder, pObj) );
            Cudd_Ref( (DdNode *)pObj->pData );
        }
    Aig_ManForEachPo( pAig, pObj, i )
        pObj->pData = Cudd_bddIthVar( dd, Llb_MnxBddVar(vOrder, pObj) );
    // compute intermediate BDDs
    vRoots = Vec_PtrAlloc( 100 );
    Aig_ManForEachNode( pAig, pObj, i )
    {
        bBdd0 = Cudd_NotCond( (DdNode *)Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0(pObj) );
        bBdd1 = Cudd_NotCond( (DdNode *)Aig_ObjFanin1(pObj)->pData, Aig_ObjFaninC1(pObj) );
        bBdd  = Cudd_bddAnd( dd, bBdd0, bBdd1 );
        Cudd_Ref( bBdd );
        if ( pObj->pData == NULL )
        {
            pObj->pData = bBdd;
            continue;
        }
        // create new partition
        bPart = Cudd_bddXnor( dd, (DdNode *)pObj->pData, bBdd );  
        if ( bPart == NULL )
            goto finish;
        Cudd_Ref( bPart );
        Cudd_RecursiveDeref( dd, bBdd );
        Vec_PtrPush( vRoots, bPart );
    }
    // compute register output BDDs
    Aig_ManForEachPo( pAig, pObj, i )
    {
        bBdd0 = Cudd_NotCond( (DdNode *)Aig_ObjFanin0(pObj)->pData, Aig_ObjFaninC0(pObj) );
        bPart = Cudd_bddXnor( dd, (DdNode *)pObj->pData, bBdd0 );  
        if ( bPart == NULL )
            goto finish;
        Cudd_Ref( bPart );
        Vec_PtrPush( vRoots, bPart );
//printf( "%d ", Cudd_DagSize(bPart) );
    }
//printf( "\n" );
    Aig_ManForEachNode( pAig, pObj, i )
        Cudd_RecursiveDeref( dd, (DdNode *)pObj->pData );
    return vRoots;
    // early termination
finish:
    Aig_ManForEachNode( pAig, pObj, i )
        if ( pObj->pData )
            Cudd_RecursiveDeref( dd, (DdNode *)pObj->pData );
    Vec_PtrForEachEntry( DdNode *, vRoots, bPart, i )
        Cudd_RecursiveDeref( dd, bPart );
    Vec_PtrFree( vRoots );
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Creates quantifiable varaibles for both types of traversal.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Llb_Nonlin4FindVars2Q( DdManager * dd, Aig_Man_t * pAig, Vec_Int_t * vOrder )
{
    Vec_Int_t * vVars2Q;
    Aig_Obj_t * pObj;
    int i;
    vVars2Q = Vec_IntAlloc( 0 );
    Vec_IntFill( vVars2Q, Cudd_ReadSize(dd), 1 );
    Saig_ManForEachLo( pAig, pObj, i )
        Vec_IntWriteEntry( vVars2Q, Llb_MnxBddVar(vOrder, pObj), 0 );
    Aig_ManForEachPo( pAig, pObj, i )
        Vec_IntWriteEntry( vVars2Q, Llb_MnxBddVar(vOrder, pObj), 0 );
    return vVars2Q;
}

/**Function*************************************************************

  Synopsis    [Creates quantifiable varaibles for both types of traversal.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Llb_Nonlin4CountTerms( DdManager * dd, Aig_Man_t * pAig, Vec_Int_t * vOrder, DdNode * bFunc, int fCo, int fFlop )
{
    DdNode * bSupp;
    Aig_Obj_t * pObj;
    int i, Counter = 0;
    bSupp = Cudd_Support( dd, bFunc );  Cudd_Ref( bFunc );
    if ( !fCo && !fFlop )
    {
        Saig_ManForEachPi( pAig, pObj, i )
            Counter += Cudd_bddLeq( dd, bSupp, Cudd_bddIthVar(dd, Llb_MnxBddVar(vOrder, pObj)) );
    }
    else if ( fCo && !fFlop )
    {
        Saig_ManForEachPo( pAig, pObj, i )
            Counter += Cudd_bddLeq( dd, bSupp, Cudd_bddIthVar(dd, Llb_MnxBddVar(vOrder, pObj)) );
    }
    else if ( !fCo && fFlop )
    {
        Saig_ManForEachLo( pAig, pObj, i )
            Counter += Cudd_bddLeq( dd, bSupp, Cudd_bddIthVar(dd, Llb_MnxBddVar(vOrder, pObj)) );
    }
    else if ( fCo && fFlop )
    {
        Saig_ManForEachLi( pAig, pObj, i )
            Counter += Cudd_bddLeq( dd, bSupp, Cudd_bddIthVar(dd, Llb_MnxBddVar(vOrder, pObj)) );
    }
    Cudd_RecursiveDeref( dd, bFunc );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Creates quantifiable varaibles for both types of traversal.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_Nonlin4PrintGroups( DdManager * dd, Aig_Man_t * pAig, Vec_Int_t * vOrder, Vec_Ptr_t * vGroups )
{
    DdNode * bTemp;
    int i, nSuppAll, nSuppPi, nSuppPo, nSuppLi, nSuppLo, nSuppAnd;
    Vec_PtrForEachEntry( DdNode *, vGroups, bTemp, i )
    {
        nSuppAll = Cudd_SupportSize(dd,bTemp);
        nSuppPi  = Llb_Nonlin4CountTerms(dd, pAig, vOrder, bTemp, 0, 0);
        nSuppPo  = Llb_Nonlin4CountTerms(dd, pAig, vOrder, bTemp, 1, 0);
        nSuppLi  = Llb_Nonlin4CountTerms(dd, pAig, vOrder, bTemp, 0, 1);
        nSuppLo  = Llb_Nonlin4CountTerms(dd, pAig, vOrder, bTemp, 1, 1);
        nSuppAnd = nSuppAll - (nSuppPi+nSuppPo+nSuppLi+nSuppLo);

        printf( "%4d : bdd =%6d  supp =%3d  ", i, Cudd_DagSize(bTemp), nSuppAll );
        printf( "pi =%3d ",  nSuppPi );
        printf( "po =%3d ",  nSuppPo );
        printf( "lo =%3d ",  nSuppLo );
        printf( "li =%3d ",  nSuppLi );
        printf( "and =%3d",  nSuppAnd );
        printf( "\n" );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Llb_Nonlin4Cluster( Aig_Man_t * pAig )
{
    DdManager * dd;
    Vec_Int_t * vOrder, * vVars2Q;
    Vec_Ptr_t * vParts, * vGroups;
    DdNode * bTemp;
    int i;

    // create the BDD manager
    dd      = Cudd_Init( Aig_ManObjNumMax(pAig), 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
//    Cudd_AutodynEnable( p->dd,  CUDD_REORDER_SYMM_SIFT );
    vOrder  = Llb_Nonlin4FindOrder( pAig );
    vVars2Q = Llb_Nonlin4FindVars2Q( dd, pAig, vOrder );
    vParts  = Llb_Nonlin4FindPartitions( dd, pAig, vOrder );

    vGroups = Llb_Nonlin4Group( dd, vParts, vVars2Q, 500 );

    Llb_Nonlin4PrintGroups( dd, pAig, vOrder, vGroups );

    Vec_PtrForEachEntry( DdNode *, vGroups, bTemp, i )
        Cudd_RecursiveDeref( dd, bTemp );

    Vec_PtrForEachEntry( DdNode *, vParts, bTemp, i )
        Cudd_RecursiveDeref( dd, bTemp );
    Extra_StopManager( dd );
//    Cudd_Quit( dd );

    Vec_IntFree( vOrder );
    Vec_IntFree( vVars2Q );
    Vec_PtrFree( vParts );
    Vec_PtrFree( vGroups );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

