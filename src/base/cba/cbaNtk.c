/**CFile****************************************************************

  FileName    [cbaNtk.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Hierarchical word-level netlist.]

  Synopsis    [Netlist manipulation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 29, 2014.]

  Revision    [$Id: cbaNtk.c,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cba.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_ManAssignInternNamesNtk( Cba_Ntk_t * p )
{
    char Buffer[100];
    int i, iObj, iTerm, NameId, fFound, nNameLess = 0;
    int nDigits = Abc_Base10Log( Cba_NtkObjNum(p) );
    // PI/PO should have NameId
    Cba_NtkForEachPi( p, iObj, i )
        assert( Cba_ObjName(p, iObj) );
    Cba_NtkForEachPo( p, iObj, i )
        assert( Cba_ObjName(p, iObj) );
    // user BI/BO should have NameId
    Cba_NtkForEachBoxUser( p, iObj )
    {
        Cba_BoxForEachBi( p, iObj, iTerm, i )
            assert( Cba_ObjName(p, iTerm) );
        Cba_BoxForEachBo( p, iObj, iTerm, i )
            assert( Cba_ObjName(p, iTerm) );
    }
    // check missing IDs
    Cba_NtkForEachBoxPrim( p, iObj )
    {
        Cba_BoxForEachBi( p, iObj, iTerm, i )
            nNameLess += !Cba_ObjName(p, iTerm);
        Cba_BoxForEachBo( p, iObj, iTerm, i )
            nNameLess += !Cba_ObjName(p, iTerm);
    }
    if ( !nNameLess )
        return;
    // create names for prim BO
    Cba_NtkForEachBoxPrim( p, iObj )
        Cba_BoxForEachBo( p, iObj, iTerm, i )
        {
            if ( Cba_ObjName(p, iTerm) )
                continue;
            sprintf( Buffer, "%s%0*d", "_n_", nDigits, iTerm );
            NameId = Abc_NamStrFindOrAdd( p->pDesign->pStrs, Buffer, &fFound );
            assert( !fFound );
            Cba_ObjSetName( p, iTerm, NameId );
        }
    // transfer names for prim BI
    Cba_NtkForEachBoxPrim( p, iObj )
        Cba_BoxForEachBi( p, iObj, iTerm, i )
        {
            if ( Cba_ObjName(p, iTerm) )
                continue;
            assert( Cba_ObjName(p, Cba_ObjFanin(p, iTerm)) );
            Cba_ObjSetName( p, iTerm, Cba_ObjName(p, Cba_ObjFanin(p, iTerm)) );
        }
}
void Cba_ManAssignInternNames( Cba_Man_t * p )
{
    Cba_Ntk_t * pNtk; int i;
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_ManAssignInternNamesNtk( pNtk );
}


/**Function*************************************************************

  Synopsis    [Count number of objects after collapsing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cba_ManClpObjNum_rec( Cba_Ntk_t * p )
{
    int i, Counter = 0;
    if ( p->Count >= 0 )
        return p->Count;
    Cba_NtkForEachBox( p, i )
        Counter += Cba_ObjIsBoxUser(p, i) ? Cba_ManClpObjNum_rec( Cba_BoxNtk(p, i) ) : Cba_BoxSize(p, i);
    return (p->Count = Counter);
}
int Cba_ManClpObjNum( Cba_Man_t * p )
{
    Cba_Ntk_t * pNtk; int i;
    Cba_ManForEachNtk( p, pNtk, i )
        pNtk->Count = -1;
    return Cba_NtkPioNum( Cba_ManRoot(p) ) + Cba_ManClpObjNum_rec( Cba_ManRoot(p) );
}

/**Function*************************************************************

  Synopsis    [Collects boxes in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_NtkDfs_rec( Cba_Ntk_t * p, int iObj, Vec_Int_t * vBoxes )
{
    int k, iFanin;
    if ( Cba_ObjIsBo(p, iObj) == 1 )
    {
        Cba_NtkDfs_rec( p, Cba_ObjFanin(p, iObj), vBoxes );
        return;
    }
    assert( Cba_ObjIsPi(p, iObj) || Cba_ObjIsBox(p, iObj) );
    if ( Cba_ObjCopy(p, iObj) > 0 ) // visited
        return;
    Cba_ObjSetCopy( p, iObj, 1 );
    Cba_BoxForEachFanin( p, iObj, iFanin, k )
        Cba_NtkDfs_rec( p, iFanin, vBoxes );
    Vec_IntPush( vBoxes, iObj );
}
Vec_Int_t * Cba_NtkDfs( Cba_Ntk_t * p )
{
    int i, iObj;
    Vec_Int_t * vBoxes = Vec_IntAlloc( Cba_NtkBoxNum(p) );
    Cba_NtkStartCopies( p ); // -1 = not visited; 1 = finished
    Cba_NtkForEachPi( p, iObj, i )
        Cba_ObjSetCopy( p, iObj, 1 );
    Cba_NtkForEachPo( p, iObj, i )
        Cba_NtkDfs_rec( p, Cba_ObjFanin(p, iObj), vBoxes );
    return vBoxes;
}

/**Function*************************************************************

  Synopsis    [Collects user boxes in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cba_NtkDfsUserBoxes_rec( Cba_Ntk_t * p, int iObj, Vec_Int_t * vBoxes )
{
    int k, iFanin;
    assert( Cba_ObjIsBoxUser(p, iObj) );
    if ( Cba_ObjCopy(p, iObj) == 1 ) // visited
        return 1;
    if ( Cba_ObjCopy(p, iObj) == 0 ) // loop
        return 0;
    Cba_ObjSetCopy( p, iObj, 0 );
    Cba_BoxForEachFanin( p, iObj, iFanin, k )
        if ( Cba_ObjIsBo(p, iFanin) && Cba_ObjIsBoxUser(p, Cba_ObjFanin(p, iFanin)) )
            if ( !Cba_NtkDfsUserBoxes_rec( p, Cba_ObjFanin(p, iFanin), vBoxes ) )
                return 0;
    Vec_IntPush( vBoxes, iObj );
    Cba_ObjSetCopy( p, iObj, 1 );
    return 1;
}
int Cba_NtkDfsUserBoxes( Cba_Ntk_t * p )
{
    int iObj;
    Cba_NtkStartCopies( p ); // -1 = not visited; 0 = on the path; 1 = finished
    Vec_IntClear( &p->vArray );
    Cba_NtkForEachBoxUser( p, iObj )
        if ( !Cba_NtkDfsUserBoxes_rec( p, iObj, &p->vArray ) )
        {
            printf( "Cyclic dependency of user boxes is detected.\n" );
            return 0;
        }
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_NtkCollapse_rec( Cba_Ntk_t * pNew, Cba_Ntk_t * p, Vec_Int_t * vSigs )
{
    int i, k, iObj, iTerm;
    Cba_NtkStartCopies( p );
    // set PI copies
    assert( Vec_IntSize(vSigs) == Cba_NtkPiNum(p) );
    Cba_NtkForEachPi( p, iObj, i )
        Cba_ObjSetCopy( p, iObj, Vec_IntEntry(vSigs, i) );
    // duplicate internal objects
    Cba_NtkForEachBox( p, iObj )
        if ( Cba_ObjIsBoxPrim(p, iObj) )
            Cba_BoxDup( pNew, p, iObj );
    // duplicate user moduled in DFS order
    Vec_IntForEachEntry( &p->vArray, iObj, i )
    {
        assert( Cba_ObjIsBoxUser(p, iObj) );
        Vec_IntClear( vSigs );
        Cba_BoxForEachBi( p, iObj, iTerm, k )
            Vec_IntPush( vSigs, Cba_ObjCopy(p, Cba_ObjFanin(p, iTerm)) );
        Cba_NtkCollapse_rec( pNew, Cba_BoxNtk(p, iObj), vSigs );
        assert( Vec_IntSize(vSigs) == Cba_BoxBoNum(p, iObj) );
        Cba_BoxForEachBo( p, iObj, iTerm, k )
            Cba_ObjSetCopy( p, iTerm, Vec_IntEntry(vSigs, k) );
    }
    // connect objects
    Cba_NtkForEachBi( p, iObj )
        Cba_ObjSetFanin( pNew, Cba_ObjCopy(p, iObj), Cba_ObjCopy(p, Cba_ObjFanin(p, iObj)) );
    // collect POs
    Vec_IntClear( vSigs );
    Cba_NtkForEachPo( p, iObj, i )
        Vec_IntPush( vSigs, Cba_ObjCopy(p, Cba_ObjFanin(p, iObj)) );
}
Cba_Man_t * Cba_ManCollapseInt( Cba_Man_t * p )
{
    int i, iObj;
    Vec_Int_t * vSigs = Vec_IntAlloc( 1000 );
    Cba_Man_t * pNew = Cba_ManStart( p, 1 );
    Cba_Ntk_t * pRoot = Cba_ManRoot( p );
    Cba_Ntk_t * pRootNew = Cba_ManRoot( pNew );
    Cba_NtkAlloc( pRootNew, Cba_NtkNameId(pRoot), Cba_NtkPiNum(pRoot), Cba_NtkPoNum(pRoot), Cba_ManClpObjNum(p) );
    Cba_NtkForEachPi( pRoot, iObj, i )
        Vec_IntPush( vSigs, Cba_ObjAlloc(pRootNew, CBA_OBJ_PI, i, -1) );
    Cba_NtkCollapse_rec( pRootNew, pRoot, vSigs );
    assert( Vec_IntSize(vSigs) == Cba_NtkPoNum(pRoot) );
    Cba_NtkForEachPo( pRoot, iObj, i )
        Cba_ObjAlloc( pRootNew, CBA_OBJ_PO, i, Vec_IntEntry(vSigs, i) );
    assert( Cba_NtkObjNum(pRootNew) == Cba_NtkAllocNum(pRootNew) );
    Vec_IntFree( vSigs );
    // transfer PI/PO names
    Cba_NtkStartNames( pRootNew );
    Cba_NtkForEachPo( pRoot, iObj, i )
        Cba_ObjSetName( pRootNew, Cba_NtkPo(pRootNew, i), Cba_ObjName(pRoot, iObj) );
    Cba_NtkForEachPo( pRoot, iObj, i )
        Cba_ObjSetName( pRootNew, Cba_NtkPo(pRootNew, i), Cba_ObjName(pRoot, iObj) );
    return pNew;
}
Cba_Man_t * Cba_ManCollapse( Cba_Man_t * p )
{
    Cba_Ntk_t * pNtk; int i;
    Cba_ManForEachNtk( p, pNtk, i )
        if ( !Cba_NtkDfsUserBoxes(pNtk) )
            return NULL;
    return Cba_ManCollapseInt( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

