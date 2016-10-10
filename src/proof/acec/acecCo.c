/**CFile****************************************************************

  FileName    [acecCo.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [CEC for arithmetic circuits.]

  Synopsis    [Core procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: acecCo.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "acecInt.h"
#include "misc/vec/vecWec.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Collect non-XOR inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_PolynCoreNonXors_rec( Gia_Man_t * pGia, Gia_Obj_t * pObj, Vec_Int_t * vXorPairs )
{
    Gia_Obj_t * pFan0, * pFan1;
    if ( !Gia_ObjRecognizeExor(pObj, &pFan0, &pFan1) )
        return;
    Gia_PolynCoreNonXors_rec( pGia, Gia_Regular(pFan0), vXorPairs );
    Gia_PolynCoreNonXors_rec( pGia, Gia_Regular(pFan1), vXorPairs );
    Vec_IntPushTwo( vXorPairs, Gia_ObjId(pGia, Gia_Regular(pFan0)), Gia_ObjId(pGia, Gia_Regular(pFan1)) );
}
Vec_Int_t * Gia_PolynAddHaRoots( Gia_Man_t * pGia )
{
    int i, iFan0, iFan1;
    Vec_Int_t * vNewOuts = Vec_IntAlloc( 100 );
    Vec_Int_t * vXorPairs = Vec_IntAlloc( 100 );
    Gia_Obj_t * pObj = Gia_ManCo( pGia, Gia_ManCoNum(pGia)-1 );
    Gia_PolynCoreNonXors_rec( pGia, Gia_ObjFanin0(pObj), vXorPairs );
    // add new outputs
    Gia_ManSetPhase( pGia );
    Vec_IntForEachEntryDouble( vXorPairs, iFan0, iFan1, i )
    {
        Gia_Obj_t * pFan0 = Gia_ManObj( pGia, iFan0 );
        Gia_Obj_t * pFan1 = Gia_ManObj( pGia, iFan1 );
        int iLit0 = Abc_Var2Lit( iFan0, pFan0->fPhase );
        int iLit1 = Abc_Var2Lit( iFan1, pFan1->fPhase );
        int iRoot = Gia_ManAppendAnd( pGia, iLit0, iLit1 );
        Vec_IntPush( vNewOuts, Abc_Lit2Var(iRoot) );
    }
    Vec_IntFree( vXorPairs );
    Vec_IntReverseOrder( vNewOuts );
//    Vec_IntPop( vNewOuts );
    return vNewOuts;
}


/**Function*************************************************************

  Synopsis    [Detects the order of adders.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_PolynCoreOrder( Gia_Man_t * pGia, Vec_Int_t * vAdds, Vec_Int_t * vAddCos, Vec_Int_t ** pvIns, Vec_Int_t ** pvOuts )
{
    Vec_Int_t * vOrder  = Vec_IntAlloc( 1000 );
    Vec_Bit_t * vIsRoot = Vec_BitStart( Gia_ManObjNum(pGia) );
    Vec_Int_t * vRoots  = Vec_IntAlloc( 5 * Gia_ManCoNum(pGia) );
    Vec_Int_t * vLeaves = Vec_IntAlloc( 2 * Gia_ManCiNum(pGia) );
    Vec_Wec_t * vMap    = Vec_WecStart( Gia_ManObjNum(pGia) );
    int i, k, Index, Driver, Entry1, Entry2 = -1;
    // nodes driven by adders into adder indexes
    for ( i = 0; 5*i < Vec_IntSize(vAdds); i++ )
    {
        Entry1 = Vec_IntEntry( vAdds, 5*i + 3 );
        Entry2 = Vec_IntEntry( vAdds, 5*i + 4 );
        Vec_WecPush( vMap, Entry1, i );
        Vec_WecPush( vMap, Entry1, Entry2 );
        Vec_WecPush( vMap, Entry2, i );
        Vec_WecPush( vMap, Entry2, Entry1 );
    }
    // collect roots
    Gia_ManForEachCoDriverId( pGia, Driver, i )
    {
        Vec_IntPush( vRoots, Driver );
        Vec_BitWriteEntry( vIsRoot, Driver, 1 );
    }
    // collect additional outputs
    Vec_IntForEachEntry( vAddCos, Driver, i )
    {
        Vec_IntPush( vRoots, Driver );
        Vec_BitWriteEntry( vIsRoot, Driver, 1 );
    }
    // detect full adder tree
    *pvOuts = Vec_IntDup( vRoots );
    while ( 1 )
    {
        // iterate through boxes driving this one
        Vec_IntForEachEntry( vRoots, Entry1, i )
        {
            Vec_Int_t * vLevel = Vec_WecEntry( vMap, Entry1 );
            Vec_IntForEachEntryDouble( vLevel, Index, Entry2, k )
                if ( Vec_BitEntry(vIsRoot, Entry2) )
                    break;
            if ( k == Vec_IntSize(vLevel) )
                continue;
            assert( Vec_BitEntry(vIsRoot, Entry1) );
            assert( Vec_BitEntry(vIsRoot, Entry2) );
            // collect adder
            Vec_IntPush( vOrder, Index );
            // clean marks
            Vec_BitWriteEntry( vIsRoot, Entry1, 0 );
            Vec_BitWriteEntry( vIsRoot, Entry2, 0 );
            Vec_IntRemove( vRoots, Entry1 );
            Vec_IntRemove( vRoots, Entry2 );
            // set new marks
            Entry1 = Vec_IntEntry( vAdds, 5*Index + 0 );
            Entry2 = Vec_IntEntry( vAdds, 5*Index + 1 );
            Driver = Vec_IntEntry( vAdds, 5*Index + 2 );
            Vec_BitWriteEntry( vIsRoot, Entry1, 1 );
            Vec_BitWriteEntry( vIsRoot, Entry2, 1 );
            Vec_BitWriteEntry( vIsRoot, Driver, 1 );
            Vec_IntPushUnique( vRoots, Entry1 );
            Vec_IntPushUnique( vRoots, Entry2 );
            Vec_IntPushUnique( vRoots, Driver );
            break;
        }
        if ( i == Vec_IntSize(vRoots) )
            break;
    }
    // collect remaining leaves
    Vec_BitForEachEntryStart( vIsRoot, Driver, i, 1 )
        if ( Driver )
            Vec_IntPush( vLeaves, i );
    *pvIns = vLeaves;
    // cleanup
    Vec_BitFree( vIsRoot );
    Vec_IntFree( vRoots );
    Vec_WecFree( vMap );
    return vOrder;
}

/**Function*************************************************************

  Synopsis    [Collect internal node order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_PolynCoreCollect_rec( Gia_Man_t * pGia, int iObj, Vec_Int_t * vNodes, Vec_Bit_t * vVisited )
{
    if ( Vec_BitEntry(vVisited, iObj) )
        return;
    Vec_BitSetEntry( vVisited, iObj, 1 );
    Gia_PolynCoreCollect_rec( pGia, Gia_ObjFaninId0p(pGia, Gia_ManObj(pGia, iObj)), vNodes, vVisited );
    Gia_PolynCoreCollect_rec( pGia, Gia_ObjFaninId1p(pGia, Gia_ManObj(pGia, iObj)), vNodes, vVisited );
    Vec_IntPush( vNodes, iObj );
}
Vec_Int_t * Gia_PolynCoreCollect( Gia_Man_t * pGia, Vec_Int_t * vAdds, Vec_Int_t * vOrder )
{
    Vec_Int_t * vNodes = Vec_IntAlloc( 1000 );
    Vec_Bit_t * vVisited = Vec_BitStart( Gia_ManObjNum(pGia) );
    int i, Index, Entry1, Entry2, Entry3;
    Vec_IntForEachEntryReverse( vOrder, Index, i )
    {
        // mark inputs
        Entry1 = Vec_IntEntry( vAdds, 5*Index + 0 );
        Entry2 = Vec_IntEntry( vAdds, 5*Index + 1 );
        Entry3 = Vec_IntEntry( vAdds, 5*Index + 2 );
        Vec_BitWriteEntry( vVisited, Entry1, 1 );
        Vec_BitWriteEntry( vVisited, Entry2, 1 );
        Vec_BitWriteEntry( vVisited, Entry3, 1 );
        // traverse from outputs
        Entry1 = Vec_IntEntry( vAdds, 5*Index + 3 );
        Entry2 = Vec_IntEntry( vAdds, 5*Index + 4 );
        Gia_PolynCoreCollect_rec( pGia, Entry1, vNodes, vVisited );
        Gia_PolynCoreCollect_rec( pGia, Entry2, vNodes, vVisited );
    }
    Vec_BitFree( vVisited );
    return vNodes;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Gia_PolynCorePrintCones( Gia_Man_t * pGia, Vec_Int_t * vLeaves, int fVerbose )
{
    int i, iObj;
    if ( fVerbose )
    {
        Vec_IntForEachEntry( vLeaves, iObj, i )
        {
            printf( "%4d : ", i );
            printf( "Supp = %3d  ", Gia_ManSuppSize(pGia, &iObj, 1) );
            printf( "Cone = %3d  ", Gia_ManConeSize(pGia, &iObj, 1) );
            printf( "\n" );
        }
    }
    else
    {
        int SuppMax = 0, ConeMax = 0;
        Vec_IntForEachEntry( vLeaves, iObj, i )
        {
            SuppMax = Abc_MaxInt( SuppMax, Gia_ManSuppSize(pGia, &iObj, 1) );
            ConeMax = Abc_MaxInt( ConeMax, Gia_ManConeSize(pGia, &iObj, 1) );
        }
        printf( "Remaining cones:  Count = %d.  SuppMax = %d.  ConeMax = %d.\n", Vec_IntSize(vLeaves), SuppMax, ConeMax );
    }
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Gia_PolynCoreDupTreePlus_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj )
{
    if ( ~pObj->Value )
        return pObj->Value;
    assert( Gia_ObjIsAnd(pObj) );
    Gia_PolynCoreDupTreePlus_rec( pNew, p, Gia_ObjFanin0(pObj) );
    Gia_PolynCoreDupTreePlus_rec( pNew, p, Gia_ObjFanin1(pObj) );
    return pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
} 
Gia_Man_t * Gia_PolynCoreDupTree( Gia_Man_t * p, Vec_Int_t * vAddCos, Vec_Int_t * vLeaves, Vec_Int_t * vNodes, int fAddCones )
{
    Gia_Man_t * pNew;
    Gia_Obj_t * pObj;
    int i;
    assert( Gia_ManRegNum(p) == 0 );
    Gia_ManFillValue( p );
    pNew = Gia_ManStart( Gia_ManObjNum(p) );
    pNew->pName = Abc_UtilStrsav( p->pName );
    pNew->pSpec = Abc_UtilStrsav( p->pSpec );
    Gia_ManConst0(p)->Value = 0;
    if ( fAddCones )
    {
        Gia_ManForEachPi( p, pObj, i )
            pObj->Value = Gia_ManAppendCi(pNew);
        Gia_ManForEachObjVec( vLeaves, p, pObj, i )
            pObj->Value = Gia_PolynCoreDupTreePlus_rec( pNew, p, pObj );
    }
    else
    {
        Gia_ManForEachObjVec( vLeaves, p, pObj, i )
            pObj->Value = Gia_ManAppendCi(pNew);
    }
    Gia_ManForEachObjVec( vNodes, p, pObj, i )
        pObj->Value = Gia_ManAppendAnd( pNew, Gia_ObjFanin0Copy(pObj), Gia_ObjFanin1Copy(pObj) );
    Gia_ManForEachCo( p, pObj, i )
        Gia_ManAppendCo( pNew, Gia_ObjFanin0Copy(pObj) );
    Gia_ManForEachObjVec( vAddCos, p, pObj, i )
        Gia_ManAppendCo( pNew, pObj->Value );
    return pNew;

}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Man_t * Gia_PolynCoreDetectTest_int( Gia_Man_t * pGia, Vec_Int_t * vAddCos, int fAddCones, int fVerbose )
{
    extern Vec_Int_t * Ree_ManComputeCuts( Gia_Man_t * p, int fVerbose );
    abctime clk = Abc_Clock();
    Gia_Man_t * pNew;
    Vec_Int_t * vAdds = Ree_ManComputeCuts( pGia, 1 );
    Vec_Int_t * vLeaves, * vRoots, * vOrder = Gia_PolynCoreOrder( pGia, vAdds, vAddCos, &vLeaves, &vRoots );
    Vec_Int_t * vNodes = Gia_PolynCoreCollect( pGia, vAdds, vOrder );
    printf( "Detected %d FAs/HAs. Roots = %d. Leaves = %d. Nodes = %d. Adds = %d. ", 
        Vec_IntSize(vAdds), Vec_IntSize(vLeaves), Vec_IntSize(vRoots), Vec_IntSize(vNodes), Vec_IntSize(vOrder) );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );

    Gia_PolynCorePrintCones( pGia, vLeaves, fVerbose );

    pNew = Gia_PolynCoreDupTree( pGia, vAddCos, vLeaves, vNodes, fAddCones );

    Vec_IntFree( vAdds );
    Vec_IntFree( vLeaves );
    Vec_IntFree( vRoots );
    Vec_IntFree( vOrder );
    Vec_IntFree( vNodes );
    return pNew;
}
Gia_Man_t * Gia_PolynCoreDetectTest( Gia_Man_t * pGia, int fAddExtra, int fAddCones, int fVerbose )
{
    Vec_Int_t * vAddCos = fAddExtra ? Gia_PolynAddHaRoots( pGia ) : Vec_IntAlloc(0);
    Gia_Man_t * pNew = Gia_PolynCoreDetectTest_int( pGia, vAddCos, fAddCones, fVerbose );
    printf( "On top of %d COs, created %d new adder outputs.\n", Gia_ManCoNum(pGia), Vec_IntSize(vAddCos) );
    Vec_IntFree( vAddCos );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

