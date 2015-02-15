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

  Synopsis    [Assigns word-level names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cba_ManAssignInternTwo( Cba_Ntk_t * p, int iNum, Vec_Int_t * vMap )
{
    char Buffer[16];
    int i = 0, NameId, nDigits;
    do
    {
        nDigits = Abc_Base10Log( Cba_NtkObjNum(p) );
        if ( i == 0 )
            sprintf( Buffer, "%s%0*d", "n", nDigits, iNum );
        else
            sprintf( Buffer, "%s%0*d_%d", "n", nDigits, iNum, ++i );
        NameId = Abc_NamStrFindOrAdd( p->pDesign->pStrs, Buffer, NULL );
    }
    while ( Vec_IntEntry(vMap, NameId) );
    Vec_IntWriteEntry( vMap, NameId, iNum );
    return NameId;
}
void Cba_ManPrepareBitNames( Cba_Ntk_t * p, Vec_Int_t * vMap, int * pnNames, Vec_Int_t * vRanges, Vec_Int_t * vNames )
{
    int n = 0, i, k, Range;
    Vec_IntClear( vNames );
    Vec_IntForEachEntry( vRanges, Range, i )
    {
        assert( Range > 0 );
        if ( Range == 1 )
            Vec_IntPush( vNames, Abc_Var2Lit2( Cba_ManAssignInternTwo(p, (*pnNames)++, vMap), CBA_NAME_BIN ) );
        else
        {
            Vec_IntPush( vNames, Abc_Var2Lit2( Cba_ManAssignInternTwo(p, (*pnNames)++, vMap), CBA_NAME_WORD ) );
            for ( k = 1; k < Range; k++ )
                Vec_IntPush( vNames, Abc_Var2Lit2( k, CBA_NAME_INDEX ) );
        }
    }
}
void Cba_ManAssignInternWordNamesNtk( Cba_Ntk_t * p, Vec_Int_t * vMap, Vec_Int_t * vRanges, Vec_Int_t * vNames )
{
    int k, n = 0, iObj, iTerm, nNames = 1;
    assert( Cba_NtkReadRangesUser(p, NULL, 0) == Cba_NtkPiNum(p) );
    assert( Cba_NtkReadRangesUser(p, NULL, 1) == Cba_NtkPoNum(p) );
    // start names
    assert( !Cba_NtkHasNames(p) );
    Cba_NtkStartNames(p);
    // derive PI names
    Cba_NtkReadRangesUser( p, vRanges, 0 );
    Cba_ManPrepareBitNames( p, vMap, &nNames, vRanges, vNames );
    assert( Vec_IntSize(vNames) == Cba_NtkPiNum(p) );
    Cba_NtkForEachPi( p, iObj, k )
    {
        Cba_ObjSetName( p, iObj, Vec_IntEntry(vNames, k) );
        if ( Cba_ObjNameType(p, iObj) <= CBA_NAME_WORD ) // works only if the PIs are before POs
            Cba_NtkSetInfoName( p, n++, Abc_Var2Lit2(Cba_ObjNameId(p, iObj), 1) );
    }
    assert( n == Vec_IntSize(vRanges) );
    // derive box output names
    Cba_NtkForEachBox( p, iObj )
    {
        if ( Cba_ObjIsBoxUser(p, iObj) )
            Cba_NtkReadRangesUser( Cba_BoxNtk(p, iObj), vRanges, 1 );
        else if ( Cba_BoxNtkId(p, iObj) )
            Cba_NtkReadRangesPrim( Cba_BoxNtkName(p, iObj), vRanges, 1 );
        else assert( 0 );
        Cba_ManPrepareBitNames( p, vMap, &nNames, vRanges, vNames );
        assert( Vec_IntSize(vNames) == Cba_BoxBoNum(p, iObj) );
        Cba_BoxForEachBo( p, iObj, iTerm, k )
            Cba_ObjSetName( p, iTerm, Vec_IntEntry(vNames, k) );
    }
    // mark PO names
    Cba_NtkReadRangesUser( p, vRanges, 1 );
    Cba_NtkForEachPo( p, iObj, k )
        if ( Cba_ObjNameType(p, Cba_ObjFanin(p, iObj)) <= CBA_NAME_WORD ) // works only if the PIs are before POs
            Cba_NtkSetInfoName( p, n++, Abc_Var2Lit2(Cba_ObjNameId(p, Cba_ObjFanin(p, iObj)), 2) );
    assert( n == Cba_NtkInfoNum(p) );
    // unmark all names
    Cba_NtkForEachPi( p, iObj, k )
        if ( Cba_ObjNameType(p, iObj) <= CBA_NAME_WORD )
            Vec_IntWriteEntry( vMap, Cba_ObjName(p, iObj), 0 );
    Cba_NtkForEachBox( p, iObj )
        Cba_BoxForEachBo( p, iObj, iTerm, k )
            if ( Cba_ObjNameType(p, iTerm) <= CBA_NAME_WORD )
                Vec_IntWriteEntry( vMap, Cba_ObjName(p, iTerm), 0 );
    printf( "Generated %d word-level names.\n", nNames-1 );
//    Vec_IntPrint( &p->vName );
//    Vec_IntPrint( &p->vInfo );
}
void Cba_ManAssignInternWordNames( Cba_Man_t * p )
{
    Vec_Int_t * vMap = Vec_IntStart( Cba_ManObjNum(p) );
    Vec_Int_t * vRanges = Vec_IntAlloc( 1000 );
    Vec_Int_t * vNames = Vec_IntAlloc( 1000 );
    Cba_Ntk_t * pNtk; int i;
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_ManAssignInternWordNamesNtk( pNtk, vMap, vRanges, vNames );
    Vec_IntFree( vMap );
    Vec_IntFree( vRanges );
    Vec_IntFree( vNames );
}


/**Function*************************************************************

  Synopsis    [Assigns bit-level names.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cba_ManSetInternOne( Cba_Ntk_t * p, int iTerm, Vec_Int_t * vMap )
{
    if ( !Cba_ObjName(p, iTerm) )
        return 1;
    if ( Cba_ObjNameType(p, iTerm) > CBA_NAME_WORD )
        return 0;
    assert( Vec_IntEntry(vMap, Cba_ObjNameId(p, iTerm)) == 0 );
    Vec_IntWriteEntry( vMap, Cba_ObjNameId(p, iTerm), iTerm+1 );
    return 0;
}
int Cba_ManAssignInternOne( Cba_Ntk_t * p, int iTerm, Vec_Int_t * vMap )
{
    char Buffer[16];
    int i = 0, NameId, nDigits;
    if ( Cba_ObjName(p, iTerm) )
        return 0;
    do
    {
        nDigits = Abc_Base10Log( Cba_NtkObjNum(p) );
        if ( i == 0 )
            sprintf( Buffer, "%s%0*d", "n", nDigits, iTerm );
        else
            sprintf( Buffer, "%s%0*d_%d", "n", nDigits, iTerm, ++i );
        NameId = Abc_NamStrFindOrAdd( p->pDesign->pStrs, Buffer, NULL );
    }
    while ( Vec_IntEntry(vMap, NameId) );
    Cba_ObjSetName( p, iTerm, Abc_Var2Lit2(NameId, CBA_NAME_BIN) );
    Vec_IntWriteEntry( vMap, NameId, iTerm+1 );
    return 1;
}
void Cba_ManAssignInternNamesNtk( Cba_Ntk_t * p, Vec_Int_t * vMap )
{
    int i, iObj, iTerm, nNameless = 0;
//    Vec_IntPrint( &p->vName );
    if ( !Cba_NtkHasNames(p) )
        Cba_NtkStartNames(p);
    // set all names
    Cba_NtkForEachPi( p, iObj, i )
        nNameless += Cba_ManSetInternOne( p, iObj, vMap );
    Cba_NtkForEachBox( p, iObj )
        Cba_BoxForEachBo( p, iObj, iTerm, i )
            nNameless += Cba_ManSetInternOne( p, iTerm, vMap );
    // generate new names
    if ( nNameless )
    {
        int nNameless2 = 0;
        Cba_NtkForEachPi( p, iObj, i )
            nNameless2 += Cba_ManAssignInternOne( p, iObj, vMap );
        Cba_NtkForEachBox( p, iObj )
            Cba_BoxForEachBo( p, iObj, iTerm, i )
                nNameless2 += Cba_ManAssignInternOne( p, iTerm, vMap );
        assert( nNameless == nNameless2 );
        if ( nNameless )
            printf( "Generated unique names for %d objects in network \"%s\".\n", nNameless, Cba_NtkName(p) );
    }
    // unmark all names
    Cba_NtkForEachPi( p, iObj, i )
        if ( Cba_ObjNameType(p, iObj) <= CBA_NAME_WORD )
            Vec_IntWriteEntry( vMap, Cba_ObjNameId(p, iObj), 0 );
    Cba_NtkForEachBox( p, iObj )
        Cba_BoxForEachBo( p, iObj, iTerm, i )
            if ( Cba_ObjNameType(p, iTerm) <= CBA_NAME_WORD )
                Vec_IntWriteEntry( vMap, Cba_ObjNameId(p, iTerm), 0 );
}
void Cba_ManAssignInternNames( Cba_Man_t * p )
{
    Vec_Int_t * vMap = Vec_IntStart( Cba_ManObjNum(p) );
    Cba_Ntk_t * pNtk; int i;
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_ManAssignInternNamesNtk( pNtk, vMap );
    Vec_IntFree( vMap );
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
        Counter += Cba_ObjIsBoxUser(p, i) ? Cba_ManClpObjNum_rec( Cba_BoxNtk(p, i) ) + 3*Cba_BoxBoNum(p, i) : Cba_BoxSize(p, i);
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
    int i, iObj, iObjNew, iTerm;
    Cba_NtkStartCopies( p );
    // set PI copies
    assert( Vec_IntSize(vSigs) == Cba_NtkPiNum(p) );
    Cba_NtkForEachPi( p, iObj, i )
        Cba_ObjSetCopy( p, iObj, Vec_IntEntry(vSigs, i) );
    // duplicate internal objects and create buffers for hierarchy instances
    Cba_NtkForEachBox( p, iObj )
        if ( Cba_ObjIsBoxPrim( p, iObj ) )
            Cba_BoxDup( pNew, p, iObj );
        else
        {
            Cba_BoxForEachBo( p, iObj, iTerm, i )
            {
                iObjNew = Cba_ObjAlloc( pNew, CBA_OBJ_BI,  -1 );
                iObjNew = Cba_ObjAlloc( pNew, CBA_BOX_BUF, -1 ); // buffer
                iObjNew = Cba_ObjAlloc( pNew, CBA_OBJ_BO,  -1 );
                Cba_ObjSetCopy( p, iTerm, iObjNew );
            }
        }
    // duplicate user modules and connect objects
    Cba_NtkForEachBox( p, iObj )
        if ( Cba_ObjIsBoxPrim( p, iObj ) )
        {
            Cba_BoxForEachBi( p, iObj, iTerm, i )
                Cba_ObjSetFanin( pNew, Cba_ObjCopy(p, iTerm), Cba_ObjCopy(p, Cba_ObjFanin(p, iTerm)) );
        }
        else
        {
            Vec_IntClear( vSigs );
            Cba_BoxForEachBi( p, iObj, iTerm, i )
                Vec_IntPush( vSigs, Cba_ObjCopy(p, Cba_ObjFanin(p, iTerm)) );
            Cba_NtkCollapse_rec( pNew, Cba_BoxNtk(p, iObj), vSigs );
            assert( Vec_IntSize(vSigs) == Cba_BoxBoNum(p, iObj) );
            Cba_BoxForEachBo( p, iObj, iTerm, i )
                Cba_ObjSetFanin( pNew, Cba_ObjCopy(p, iTerm)-2, Vec_IntEntry(vSigs, i) );
        }
    // collect POs
    Vec_IntClear( vSigs );
    Cba_NtkForEachPo( p, iObj, i )
        Vec_IntPush( vSigs, Cba_ObjCopy(p, Cba_ObjFanin(p, iObj)) );
}
Cba_Man_t * Cba_ManCollapse( Cba_Man_t * p )
{
    int i, iObj;
    Vec_Int_t * vSigs = Vec_IntAlloc( 1000 );
    Cba_Man_t * pNew = Cba_ManStart( p, 1 );
    Cba_Ntk_t * pRoot = Cba_ManRoot( p );
    Cba_Ntk_t * pRootNew = Cba_ManRoot( pNew );
    Cba_NtkAlloc( pRootNew, Cba_NtkNameId(pRoot), Cba_NtkPiNum(pRoot), Cba_NtkPoNum(pRoot), Cba_ManClpObjNum(p) );
    Cba_NtkForEachPi( pRoot, iObj, i )
        Vec_IntPush( vSigs, Cba_ObjAlloc(pRootNew, CBA_OBJ_PI, -1) );
    Cba_NtkCollapse_rec( pRootNew, pRoot, vSigs );
    assert( Vec_IntSize(vSigs) == Cba_NtkPoNum(pRoot) );
    Cba_NtkForEachPo( pRoot, iObj, i )
        Cba_ObjAlloc( pRootNew, CBA_OBJ_PO, Vec_IntEntry(vSigs, i) );
    assert( Cba_NtkObjNum(pRootNew) == Cba_NtkObjNumAlloc(pRootNew) );
    Vec_IntFree( vSigs );
    // transfer PI/PO names
    if ( Cba_NtkHasNames(pRoot) )
    {
        Cba_NtkStartNames( pRootNew );
        Cba_NtkForEachPi( pRoot, iObj, i )
            Cba_ObjSetName( pRootNew, Cba_NtkPi(pRootNew, i), Cba_ObjName(pRoot, iObj) );
        Cba_NtkForEachPoDriver( pRoot, iObj, i )
            if ( !Cba_ObjIsPi(pRoot, iObj) )
                Cba_ObjSetName( pRootNew, Cba_ObjCopy(pRoot, iObj), Cba_ObjName(pRoot, iObj) );
    }
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

