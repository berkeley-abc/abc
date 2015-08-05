/**CFile****************************************************************

  FileName    [cbaNtk.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Hierarchical word-level netlist.]

  Synopsis    [Network manipulation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - July 21, 2015.]

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

  Synopsis    [Order objects by box type and then by name.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
// compares two numbers with the first mismatching char in i-th position
static inline int Cba_CharIsDigit( char c ) { return c >= '0' && c <= '9'; }
int Cba_StrCmpInt( char * p1, char * p2, int i )
{
    // check if one of the mismatching chars is a digit
    if ( Cba_CharIsDigit(p1[i]) || Cba_CharIsDigit(p2[i]) )
    {
        // if previous (equal) char was a digit or if this is first digit on both sides, scroll back
        if ( (i > 0 && Cba_CharIsDigit(p1[i-1])) || (Cba_CharIsDigit(p1[i]) && Cba_CharIsDigit(p2[i])) )
        {
            int Num1, Num2;
            // find the first digit
            for ( --i; i >= 0; i-- )
                if ( !Cba_CharIsDigit(p1[i]) )
                    break;
            i++;
            // current char is digit
            assert( Cba_CharIsDigit(p1[i]) );
            assert( Cba_CharIsDigit(p2[i]) );
            // previous char does not exist or is not a digit
            assert( i == 0 || !Cba_CharIsDigit(p1[i-1]) );
            assert( i == 0 || !Cba_CharIsDigit(p2[i-1]) );
            // compare numbers
            Num1 = atoi( p1 + i );
            Num2 = atoi( p2 + i );
            if ( Num1 < Num2 )
                return -1;
            if ( Num1 > Num2 ) 
                return 1;
            assert( 0 );
            return 0;
        }
    }
    // compare as usual
    if ( p1[i] < p2[i] )
        return -1;
    if ( p1[i] > p2[i] )
        return 1;
    assert( 0 );
    return 0;
}
int Cba_StrCmp( char ** pp1, char ** pp2 )
{
    char * p1 = *pp1;
    char * p2 = *pp2; int i;
    for ( i = 0; p1[i] && p2[i]; i++ )
        if ( p1[i] != p2[i] )
            return Cba_StrCmpInt( p1, p2, i );
    assert( !p1[i] || !p2[i] );
    return Cba_StrCmpInt( p1, p2, i );
}
void Cba_NtkObjOrder( Cba_Ntk_t * p, Vec_Int_t * vObjs, Vec_Int_t * vNameIds )
{
    char Buffer[1000], * pName;
    Vec_Ptr_t * vNames;
    int i, iObj;
    if ( Vec_IntSize(vObjs) < 2 )
        return;
    vNames = Vec_PtrAlloc( Vec_IntSize(vObjs) );
    Vec_IntForEachEntry( vObjs, iObj, i )
    {
        char * pTypeName = Cba_NtkTypeName( p, Cba_ObjType(p, iObj) );
        char * pInstName = vNameIds ? Cba_NtkStr(p, Vec_IntEntry(vNameIds, i)) : Cba_ObjNameStr(p, iObj);
        sprintf( Buffer, "%s_%s_%d", pTypeName, pInstName, iObj );
        Vec_PtrPush( vNames, Abc_UtilStrsav(Buffer) );
    }
    // print before
//    Vec_PtrForEachEntry( char *, vNames, pName, i )
//        printf( "%s \n", pName );
//    printf( "\n" );
    // do the sorting
    Vec_PtrSort( vNames, (int (*)(void))Cba_StrCmp );
    // print after
//    Vec_PtrForEachEntry( char *, vNames, pName, i )
//        printf( "%s \n", pName );
//    printf( "\n" );
    // reload in a new order
    Vec_IntClear( vObjs );
    Vec_PtrForEachEntry( char *, vNames, pName, i )
        Vec_IntPush( vObjs, atoi(strrchr(pName, '_')+1) );
    Vec_PtrFreeFree( vNames );
}


/**Function*************************************************************

  Synopsis    [Returns the number of CI fons.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cba_NtkCiFonNum( Cba_Ntk_t * p )
{
    int i, iObj, Count = Cba_NtkPiNum(p);
    Cba_NtkForEachBoxSeq( p, iObj, i )
        Count += Cba_ObjFonNum(p, iObj);
    return Count;  
}
int Cba_NtkCoFinNum( Cba_Ntk_t * p )
{
    int i, iObj, Count = Cba_NtkPoNum(p);
    Cba_NtkForEachBoxSeq( p, iObj, i )
        Count += Cba_ObjFinNum(p, iObj);
    return Count;  
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the manager is in the topo order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cba_NtkIsTopoOrder( Cba_Ntk_t * p )
{
    int i, k, iObj, iFin, iFanin, fTopo = 1;
    Vec_Bit_t * vVisited = Vec_BitStart( Cba_NtkObjNum(p) + 1 );
    // mark PIs and seq objects
    Cba_NtkForEachPi( p, iObj, i )
        Vec_BitWriteEntry( vVisited, iObj, 1 );
    Cba_NtkForEachBoxSeq( p, iObj, i )
        Vec_BitWriteEntry( vVisited, iObj, 1 );
    // visit combinational nodes
    Cba_NtkForEachBox( p, iObj )
        if ( !Cba_ObjIsSeq(p, iObj) )
        {
            Cba_ObjForEachFinFaninReal( p, iObj, iFin, iFanin, k )
                if ( !Vec_BitEntry(vVisited, iFanin) )
                    fTopo = 0;
            if ( !fTopo )
                break;
            Vec_BitWriteEntry( vVisited, iObj, 1 );
        }
    // visit POs and seq objects
    if ( fTopo )
    Cba_NtkForEachPo( p, iObj, i )
    {
        Cba_ObjForEachFinFaninReal( p, iObj, iFin, iFanin, k )
            if ( !Vec_BitEntry(vVisited, iFanin) )
                fTopo = 0;
        if ( !fTopo )
            break;
    }
    if ( fTopo )
    Cba_NtkForEachBoxSeq( p, iObj, i )
    {
        Cba_ObjForEachFinFaninReal( p, iObj, iFin, iFanin, k )
            if ( !Vec_BitEntry(vVisited, iFanin) )
                fTopo = 0;
        if ( !fTopo )
            break;
    }
    Vec_BitFree( vVisited );
    return fTopo;
}
int Cba_ManIsTopoOrder( Cba_Man_t * p )
{
    Cba_Ntk_t * pNtk; int i;
    Cba_ManForEachNtk( p, pNtk, i )
        if ( !Cba_NtkIsTopoOrder(pNtk) )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Collects user boxes in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Cba_NtkCheckComboLoop_rec( Cba_Ntk_t * p, int iObj )
{
    int k, iFin, iFanin;
    if ( Cba_ObjIsPi(p, iObj) )
        return 1;
    if ( Cba_ObjCopy(p, iObj) == 1 ) // visited
        return 1;
    if ( Cba_ObjCopy(p, iObj) == 0 ) // loop
        return 0;
    Cba_ObjSetCopy( p, iObj, 0 );
    Cba_ObjForEachFinFaninReal( p, iObj, iFin, iFanin, k )
        if ( !Cba_ObjIsSeq(p, iFanin) )
            if ( !Cba_NtkCheckComboLoop_rec( p, iFanin ) )
                return 0;
    //Cba_ObjSetCopy( p, iObj, 1 );
    Vec_IntSetEntry( &p->vObjCopy, iObj, 1 );
    return 1;
}
int Cba_NtkCheckComboLoop( Cba_Ntk_t * p )
{
    int iObj;
    Cba_NtkCleanObjCopies( p ); // -1 = not visited; 0 = on the path; 1 = finished
    Cba_NtkForEachBox( p, iObj )
        if ( !Cba_ObjIsSeq(p, iObj) )
            if ( !Cba_NtkCheckComboLoop_rec( p, iObj ) )
            {
                printf( "Cyclic dependency of user boxes is detected.\n" );
                return 0;
            }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Collect nodes in the DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_NtkCollectDfs_rec( Cba_Ntk_t * p, int iObj, Vec_Int_t * vObjs )
{
    int iFin, iFanin, k;
    if ( !Cba_ObjCopy(p, iObj) )
        return;
    Cba_ObjSetCopy( p, iObj, 0 );
    Cba_ObjForEachFinFaninReal( p, iObj, iFin, iFanin, k )
        Cba_NtkCollectDfs_rec( p, iFanin, vObjs );
    Vec_IntPush( vObjs, iObj );
}
Vec_Int_t * Cba_NtkCollectDfs( Cba_Ntk_t * p )
{
    int i, k, iObj, iFin, iFanin;
    Vec_Int_t * vObjs = Vec_IntAlloc( Cba_NtkObjNum(p) );
    // collect PIs and seq boxes
    Cba_NtkForEachPi( p, iObj, i )
        Vec_IntPush( vObjs, iObj );
    Cba_NtkForEachBoxSeq( p, iObj, i )
        Vec_IntPush( vObjs, iObj );
    // prepare leaves
    Cba_NtkCleanObjCopies( p );
    Vec_IntForEachEntry( vObjs, iObj, i )
        Cba_ObjSetCopy( p, iObj, 0 );
    // collect internal
    Cba_NtkForEachPo( p, iObj, i )
        Cba_ObjForEachFinFaninReal( p, iObj, iFin, iFanin, k )
            Cba_NtkCollectDfs_rec( p, iFanin, vObjs );
    Cba_NtkForEachBoxSeq( p, iObj, i )
        Cba_ObjForEachFinFaninReal( p, iObj, iFin, iFanin, k )
            Cba_NtkCollectDfs_rec( p, iFanin, vObjs );
    // collect POs
    Cba_NtkForEachPo( p, iObj, i )
        Vec_IntPush( vObjs, iObj );
    assert( Vec_IntSize(vObjs) <= Cba_NtkObjNum(p) );
    if ( Vec_IntSize(vObjs) != Cba_NtkObjNum(p) )
        printf( "Warning: DSF ordering for module \"%s\" collected %d out of %d objects.\n", Cba_NtkName(p), Vec_IntSize(vObjs), Cba_NtkObjNum(p) );
    return vObjs;
}


/**Function*************************************************************

  Synopsis    [Count number of objects after collapsing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_ManGetClpStats_rec( Cba_Ntk_t * p, int * pCountN, int * pCountI, int * pCountO )
{
    int iObj, Id = Cba_NtkId(p);
    if ( pCountN[Id] >= 0 )
        return;
    pCountN[Id] = pCountI[Id] = pCountO[Id] = 0;
    Cba_NtkForEachObj( p, iObj )
        if ( Cba_ObjIsBoxPrim(p, iObj) )
        {
            pCountN[Id] += 1;
            pCountI[Id] += Cba_ObjFinNum(p, iObj);
            pCountO[Id] += Cba_ObjFonNum(p, iObj);
        }
        else if ( Cba_ObjIsBoxUser(p, iObj) )
        {
            int NtkId = Cba_ObjNtkId(p, iObj);
            Cba_ManGetClpStats_rec( Cba_ObjNtk(p, iObj), pCountN, pCountI, pCountO );
            pCountN[Id] += pCountN[NtkId] + Cba_ObjFonNum(p, iObj);
            pCountI[Id] += pCountI[NtkId] + Cba_ObjFonNum(p, iObj);
            pCountO[Id] += pCountO[NtkId] + Cba_ObjFonNum(p, iObj);
        }
}
void Cba_ManGetClpStats( Cba_Man_t * p, int * nObjs, int * nFins, int * nFons )
{
    int * pCountN = ABC_FALLOC( int, Cba_ManNtkNum(p) + 1 );
    int * pCountI = ABC_FALLOC( int, Cba_ManNtkNum(p) + 1 );
    int * pCountO = ABC_FALLOC( int, Cba_ManNtkNum(p) + 1 );
    Cba_Ntk_t * pRoot = Cba_ManRoot(p);
    Cba_ManGetClpStats_rec( pRoot, pCountN, pCountI, pCountO );
    *nObjs = Cba_NtkPioNum(pRoot) + pCountN[Cba_NtkId(pRoot)];
    *nFins = Cba_NtkPoNum(pRoot)  + pCountI[Cba_NtkId(pRoot)];
    *nFons = Cba_NtkPiNum(pRoot)  + pCountO[Cba_NtkId(pRoot)];
    ABC_FREE( pCountN );
    ABC_FREE( pCountI );
    ABC_FREE( pCountO );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_NtkCollapse_rec( Cba_Ntk_t * pNew, Cba_Ntk_t * p, Vec_Int_t * vSigs, int TypeBuf )
{
    int i, iObj, iObjNew, iFin, iFon;
    Cba_NtkCleanObjCopies( p );
    Cba_NtkCleanFonCopies( p );
    // set PI copies
    assert( Vec_IntSize(vSigs) == Cba_NtkPiNum(p) );
    Cba_NtkForEachPiFon( p, iObj, iFon, i )
        Cba_FonSetCopy( p, iFon, Vec_IntEntry(vSigs, i) );
    // duplicate primitives and create buffers for user instances
    Cba_NtkForEachObj( p, iObj )
        if ( Cba_ObjIsBoxPrim( p, iObj ) )
        {
            iObjNew = Cba_ObjDup( pNew, p, iObj );
            Cba_ObjForEachFon( p, iObj, iFon, i )
                Cba_FonSetCopy( p, iFon, Cba_ObjFon(pNew, iObjNew, i) );
            if ( Cba_ObjAttr(p, iObj) )
                Cba_ObjSetAttrs( pNew, iObjNew, Cba_ObjAttrArray(p, iObj), Cba_ObjAttrSize(p, iObj) );
        }
        else if ( Cba_ObjIsBoxUser( p, iObj ) )
        {
            Cba_ObjForEachFon( p, iObj, iFon, i )
            {
                iObjNew = Cba_ObjAlloc( pNew, TypeBuf, 1, 1 );
                Cba_FonSetCopy( p, iFon, Cba_ObjFon0(pNew, iObjNew) );
            }
        }
    // connect primitives and collapse user instances
    Cba_NtkForEachObj( p, iObj )
        if ( Cba_ObjIsBoxPrim( p, iObj ) )
        {
            iObjNew = Cba_ObjCopy( p, iObj );
            Cba_ObjForEachFinFon( p, iObj, iFin, iFon, i )
                Cba_ObjSetFinFon( pNew, iObjNew, i, Cba_FonCopy(p, iFon) );
        }
        else if ( Cba_ObjIsBoxUser( p, iObj ) )
        {
            Vec_IntClear( vSigs );
            Cba_ObjForEachFinFon( p, iObj, iFin, iFon, i )
                Vec_IntPush( vSigs, Cba_FonCopy(p, iFon) );
            assert( Vec_IntSize(vSigs) == Cba_ObjFinNum(p, iObj) );
            Cba_NtkCollapse_rec( pNew, Cba_ObjNtk(p, iObj), vSigs, TypeBuf );
            assert( Vec_IntSize(vSigs) == Cba_ObjFonNum(p, iObj) );
            Cba_ObjForEachFon( p, iObj, iFon, i )
            {
                iObjNew = Cba_FonObj( pNew, Cba_FonCopy(p, iFon) ); // buffer
                Cba_ObjSetFinFon( pNew, iObjNew, 0, Vec_IntEntry(vSigs, i) );
            }
        }
    // collect POs
    Vec_IntClear( vSigs );
    Cba_NtkForEachPoDriverFon( p, iObj, iFon, i )
        Vec_IntPush( vSigs, Cba_FonCopy(p, iFon) );
}
Cba_Man_t * Cba_ManCollapse( Cba_Man_t * p, int TypeBuf )
{
    Cba_Man_t * pNew  = Cba_ManAlloc( p->pSpec, 1, Abc_NamRef(p->pStrs), Abc_NamRef(p->pFuns), Abc_NamStart(100, 24) );
    Cba_Ntk_t * pRoot = Cba_ManRoot( p ), * pRootNew;
    Vec_Int_t * vSigs = Vec_IntAlloc( 1000 );
    int i, iObj, iObjNew, iFon, nObjs = 0, nFins = 0, nFons = 0;
    Cba_ManDupTypeNames( pNew, p );
    Cba_ManGetClpStats( p, &nObjs, &nFins, &nFons    );
    pRootNew = Cba_NtkAlloc( pNew, Cba_NtkNameId(pRoot), Cba_NtkPiNum(pRoot), Cba_NtkPoNum(pRoot), nObjs, nFins, nFons );
    Cba_NtkAdd( pNew, pRootNew );
    if ( Cba_NtkHasObjNames(pRoot) )
        Cba_NtkCleanObjNames( pRootNew );
    if ( Cba_NtkHasFonNames(pRoot) )
        Cba_NtkCleanFonNames( pRootNew );
    if ( Cba_NtkHasObjAttrs(pRoot) )
        Cba_NtkCleanObjAttrs( pRootNew );
    if ( Cba_ObjAttr(pRoot, 0) )
        Cba_ObjSetAttrs( pRootNew, 0, Cba_ObjAttrArray(pRoot, 0), Cba_ObjAttrSize(pRoot, 0) );
    Cba_NtkCleanObjCopies( pRoot );
    Cba_NtkForEachPiFon( pRoot, iObj, iFon, i )
    {
        iObjNew = Cba_ObjDup( pRootNew, pRoot, iObj );
        Vec_IntPush( vSigs, Cba_ObjFon0(pRootNew, iObjNew) );
        if ( Cba_NtkHasObjNames(pRoot) )
            Cba_ObjSetName( pRootNew, iObjNew, Cba_ObjName(pRoot, iObj) );
        if ( Cba_NtkHasFonNames(pRoot) )
            Cba_FonSetName( pRootNew, Cba_ObjFon0(pRootNew, iObjNew), Cba_FonName(pRoot, iFon) );
        if ( Cba_ObjAttr(pRoot, iObj) )
            Cba_ObjSetAttrs( pRootNew, iObjNew, Cba_ObjAttrArray(pRoot, iObj), Cba_ObjAttrSize(pRoot, iObj) );
    }
    assert( Vec_IntSize(vSigs) == Cba_NtkPiNum(pRoot) );
    Cba_NtkCollapse_rec( pRootNew, pRoot, vSigs, TypeBuf );
    assert( Vec_IntSize(vSigs) == Cba_NtkPoNum(pRoot) );
    Cba_NtkForEachPoDriverFon( pRoot, iObj, iFon, i )
    {
        iObjNew = Cba_ObjDup( pRootNew, pRoot, iObj );
        Cba_ObjSetFinFon( pRootNew, iObjNew, 0, Vec_IntEntry(vSigs, i) );
        if ( Cba_NtkHasObjNames(pRoot) )
            Cba_ObjSetName( pRootNew, iObjNew, Cba_ObjName(pRoot, iObj) );
        if ( Cba_NtkHasFonNames(pRoot) )
            Cba_FonSetName( pRootNew, Vec_IntEntry(vSigs, i), Cba_FonName(pRoot, iFon) );
        if ( Cba_ObjAttr(pRoot, iObj) )
            Cba_ObjSetAttrs( pRootNew, iObjNew, Cba_ObjAttrArray(pRoot, iObj), Cba_ObjAttrSize(pRoot, iObj) );
    }
    Vec_IntFree( vSigs );
    assert( Cba_NtkObjNum(pRootNew) == Cba_NtkObjNumAlloc(pRootNew) );
    assert( Cba_NtkFinNum(pRootNew) == Cba_NtkFinNumAlloc(pRootNew) );
    assert( Cba_NtkFonNum(pRootNew) == Cba_NtkFonNumAlloc(pRootNew) );
    // create internal node names
    Cba_NtkMissingFonNames( pRootNew, "m" );
    //Cba_NtkPrepareSeq( pRootNew );
    return pNew;
}



/**Function*************************************************************

  Synopsis    [Performs the reverse of collapsing.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Cba_NtkCollectInFons( Cba_Ntk_t * p, Vec_Int_t * vObjs )
{
    Vec_Int_t * vFons = Vec_IntAlloc( 100 );
    Vec_Bit_t * vVisFons = Vec_BitStart( Cba_NtkFonNum(p) + 1 );
    int i, k, iObj, iFin, iFon, Entry;
    // mark fanin fons
    Vec_IntForEachEntry( vObjs, iObj, i )
        Cba_ObjForEachFinFon( p, iObj, iFin, iFon, k )
            if ( iFon > 0 )
                Vec_BitWriteEntry( vVisFons, iFon, 1 );
    // unmark internal fons
    Vec_IntForEachEntry( vObjs, iObj, i )
        Cba_ObjForEachFon( p, iObj, iFon, k )
            Vec_BitWriteEntry( vVisFons, iFon, 0 );
    // collect fons
    Vec_BitForEachEntry( vVisFons, Entry, iFon )
        if ( Entry )
            Vec_IntPush( vFons, iFon );
    Vec_BitFree( vVisFons );
    return vFons;
}
Vec_Int_t * Cba_NtkCollectOutFons( Cba_Ntk_t * p, Vec_Int_t * vObjs )
{
    Vec_Int_t * vFons = Vec_IntAlloc( 100 );
    Vec_Bit_t * vMapObjs = Vec_BitStart( Cba_NtkObjNum(p) + 1 );
    Vec_Bit_t * vVisFons = Vec_BitStart( Cba_NtkFonNum(p) + 1 );
    int i, k, iObj, iFin, iFon;
    // map objects
    Vec_IntForEachEntry( vObjs, iObj, i )
        Vec_BitWriteEntry( vMapObjs, iObj, 1 );
    // mark those used by non-objects
    Cba_NtkForEachObj( p, iObj )
        if ( !Vec_BitEntry(vMapObjs, iObj) )
            Cba_ObjForEachFinFon( p, iObj, iFin, iFon, k )
                if ( iFon > 0 )
                    Vec_BitWriteEntry( vVisFons, iFon, 1 );
    // collect pointed fons among those in objects
    Vec_IntForEachEntry( vObjs, iObj, i )
        Cba_ObjForEachFon( p, iObj, iFon, k )
            if ( Vec_BitEntry(vVisFons, iFon) )
                Vec_IntPush( vFons, iFon );
    Vec_BitFree( vMapObjs );
    Vec_BitFree( vVisFons );
    return vFons;
}
void Cba_NtkCollectGroupStats( Cba_Ntk_t * p, Vec_Int_t * vObjs, int * pnFins, int * pnFons )
{
    int i, iObj, nFins = 0, nFons = 0;
    Vec_IntForEachEntry( vObjs, iObj, i )
    {
        nFins += Cba_ObjFinNum(p, iObj);
        nFons += Cba_ObjFonNum(p, iObj);
    }
    *pnFins = nFins;
    *pnFons = nFons;
}
void Cba_ManExtractGroupInt( Cba_Ntk_t * pNew, Cba_Ntk_t * p, Vec_Int_t * vObjs, Vec_Int_t * vFonIns, Vec_Int_t * vFonOuts )
{
    int i, k, iObj, iObjNew, iFin, iFon;
    Cba_NtkCleanObjCopies( p );
    Cba_NtkCleanFonCopies( p );
    // create inputs and map fons
    Vec_IntForEachEntry( vFonIns, iFon, i )
    {
        iObjNew = Cba_ObjAlloc( pNew, CBA_OBJ_PI, 0, 1 );
        Cba_FonSetCopy( p, iFon, Cba_ObjFon0(pNew, iObjNew) );
        if ( Cba_NtkHasObjNames(p) )
            Cba_ObjSetName( pNew, iObjNew, Cba_ObjName(p, Cba_FonObj(p, iFon)) );
        if ( Cba_NtkHasFonNames(p) )
            Cba_FonSetName( pNew, Cba_ObjFon0(pNew, iObjNew), Cba_FonName(p, iFon) );

    }
    // create internal
    Vec_IntForEachEntry( vObjs, iObj, i )
    {
        iObjNew = Cba_ObjDup( pNew, p, iObj );
        if ( Cba_NtkHasObjNames(p) )
            Cba_ObjSetName( pNew, iObjNew, Cba_ObjName(p, iObj) );
        Cba_ObjForEachFon( p, iObj, iFon, k )
        {
            Cba_FonSetCopy( p, iFon, Cba_ObjFon(pNew, iObjNew, k) );
            if ( Cba_NtkHasFonNames(p) )
                Cba_FonSetName( pNew, Cba_ObjFon(pNew, iObjNew, k), Cba_FonName(p, iFon) );
        }
    }
    // connect internal
    Vec_IntForEachEntry( vObjs, iObj, i )
    {
        iObjNew = Cba_ObjCopy( p, iObj );
        Cba_ObjForEachFinFon( p, iObj, iFin, iFon, k )
            Cba_ObjSetFinFon( pNew, iObjNew, k, Cba_FonCopy(p, iFon) );
    }
    // create POs
    Vec_IntForEachEntry( vFonOuts, iFon, i )
    {
        iObjNew = Cba_ObjAlloc( pNew, CBA_OBJ_PO, 1, 0 );
        if ( Cba_NtkHasObjNames(p) )
            Cba_ObjSetName( pNew, iObjNew, Cba_FonName(p, iFon) );
        Cba_ObjSetFinFon( pNew, iObjNew, 0, Cba_FonCopy(p, iFon) );
    }
    assert( Cba_NtkObjNum(pNew) == Cba_NtkObjNumAlloc(pNew) );
    assert( Cba_NtkFinNum(pNew) == Cba_NtkFinNumAlloc(pNew) );
    assert( Cba_NtkFonNum(pNew) == Cba_NtkFonNumAlloc(pNew) );
}
Cba_Man_t * Cba_ManExtractGroup( Cba_Man_t * p, Vec_Int_t * vObjs )
{
    Cba_Man_t * pNew  = Cba_ManAlloc( p->pSpec, 1, Abc_NamRef(p->pStrs), Abc_NamRef(p->pFuns), Abc_NamStart(100, 24) );
    Cba_Ntk_t * pRoot = Cba_ManRoot( p ), * pRootNew;
    Vec_Int_t * vFonIns = Cba_NtkCollectInFons( pRoot, vObjs );
    Vec_Int_t * vFonOuts = Cba_NtkCollectOutFons( pRoot, vObjs );
    int nObjs, nFins, nFons;
    Cba_ManDupTypeNames( pNew, p );
    // collect stats
    Cba_NtkCollectGroupStats( pRoot, vObjs, &nFins, &nFons );
    nObjs  = Vec_IntSize(vObjs) + Vec_IntSize(vFonIns) + Vec_IntSize(vFonOuts);
    nFins += Vec_IntSize(vFonOuts);
    nFons += Vec_IntSize(vFonIns);
    // create network
    pRootNew = Cba_NtkAlloc( pNew, Cba_NtkNameId(pRoot), Vec_IntSize(vFonIns), Vec_IntSize(vFonOuts), nObjs, nFins, nFons );
    Cba_NtkAdd( pNew, pRootNew );
    if ( Cba_NtkHasObjNames(pRoot) )
        Cba_NtkCleanObjNames( pRootNew );
    if ( Cba_NtkHasFonNames(pRoot) )
        Cba_NtkCleanFonNames( pRootNew );
    // add group nodes
    Cba_ManExtractGroupInt( pRootNew, pRoot, vObjs, vFonIns, vFonOuts );
    Cba_NtkMissingFonNames( pRootNew, "b" );
    //Cba_NtkPrepareSeq( pRootNew );
    // cleanup
    Vec_IntFree( vFonIns );
    Vec_IntFree( vFonOuts );
    return pNew;
}


/**Function*************************************************************

  Synopsis    [Derives the design from the GIA manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Cba_NtkInsertGiaLit( Cba_Ntk_t * p, int iLit, Vec_Int_t * vLit2Fon )
{
    int iObjNew;
    if ( iLit == 0 || iLit == 1 )
        return Cba_FonFromConst(iLit);
    if ( Vec_IntEntry(vLit2Fon, iLit) >= 0 )
        return Vec_IntEntry(vLit2Fon, iLit);
    assert( Abc_LitIsCompl(iLit) );
    assert( Vec_IntEntry(vLit2Fon, Abc_LitNot(iLit)) >= 0 );
    iObjNew = Cba_ObjAlloc( p, CBA_BOX_INV, 1, 1 );
    Cba_ObjSetFinFon( p, iObjNew, 0, Vec_IntEntry(vLit2Fon, Abc_LitNot(iLit)) );
    Vec_IntWriteEntry( vLit2Fon, iLit, Cba_ObjFon0(p, iObjNew) );
    return Cba_ObjFon0(p, iObjNew);
}
static inline int Cba_NtkInsertGiaObj( Cba_Ntk_t * p, Gia_Man_t * pGia, int iObj, Vec_Int_t * vLit2Fon )
{
    Gia_Obj_t * pObj = Gia_ManObj( pGia, iObj );
    int iLit0 = Gia_ObjFaninLit0( pObj, iObj );
    int iLit1 = Gia_ObjFaninLit1( pObj, iObj );
    int iFon0 = Cba_NtkInsertGiaLit( p, iLit0, vLit2Fon );
    int iFon1 = Cba_NtkInsertGiaLit( p, iLit1, vLit2Fon );
    int iObjNew;
    if ( Gia_ObjIsMux(pGia, pObj) )
    {
        int iLit2 = Gia_ObjFaninLit2( pGia, iObj );
        int iFon2 = Cba_NtkInsertGiaLit( p, iLit2, vLit2Fon );
        iObjNew = Cba_ObjAlloc( p, CBA_BOX_MUX, 3, 1 );
        Cba_ObjSetFinFon( p, iObjNew, 0, iFon2 );
        Cba_ObjSetFinFon( p, iObjNew, 1, iFon1 );
        Cba_ObjSetFinFon( p, iObjNew, 2, iFon0 );
    }
    else
    {
        assert( Gia_ObjIsAnd(pObj) );
        iObjNew = Cba_ObjAlloc( p, Gia_ObjIsXor(pObj) ? CBA_BOX_XOR : CBA_BOX_AND, 2, 1 );
        Cba_ObjSetFinFon( p, iObjNew, 0, iFon0 );
        Cba_ObjSetFinFon( p, iObjNew, 1, iFon1 );
    }
    Vec_IntWriteEntry( vLit2Fon, Abc_Var2Lit(iObj, 0), Cba_ObjFon0(p, iObjNew) );
    return iObjNew;
}
Cba_Man_t * Cba_ManDeriveFromGia( Gia_Man_t * pGia )
{
    Cba_Man_t * p = Cba_ManAlloc( pGia->pSpec, 1, NULL, NULL, NULL );
    Cba_Ntk_t * pNtk = Cba_NtkAlloc( p, Abc_NamStrFindOrAdd(p->pStrs, pGia->pName, NULL), Gia_ManCiNum(pGia), Gia_ManCoNum(pGia), 1000, 2000, 2000 );
    Vec_Int_t * vLit2Fon = Vec_IntStartFull( 2*Gia_ManObjNum(pGia) );
    int i, iObj, iObjNew, NameId, iLit0, iFon0;
    Gia_Obj_t * pObj;
    //Cba_ManPrepareTypeNames( p );
    Cba_NtkAdd( p, pNtk );
    Cba_NtkCleanObjNames( pNtk );
    Gia_ManForEachCiId( pGia, iObj, i )
    {
        NameId = pGia->vNamesIn? Abc_NamStrFindOrAdd(p->pStrs, Vec_PtrEntry(pGia->vNamesIn, i), NULL) : Cba_ManNewStrId_(p, "i", i, NULL);
        iObjNew = Cba_ObjAlloc( pNtk, CBA_OBJ_PI, 0, 1 );
        Cba_ObjSetName( pNtk, iObjNew, NameId );
        Vec_IntWriteEntry( vLit2Fon, Abc_Var2Lit(iObj, 0), Cba_ObjFon0(pNtk, iObjNew) );
    }
    Gia_ManForEachAndId( pGia, iObj )
        Cba_NtkInsertGiaObj( pNtk, pGia, iObj, vLit2Fon );
    // create inverters if needed
    Gia_ManForEachCoId( pGia, iObj, i )
    {
        pObj = Gia_ManObj( pGia, iObj );
        iLit0 = Gia_ObjFaninLit0( pObj, iObj );
        iFon0 = Cba_NtkInsertGiaLit( pNtk, iLit0, vLit2Fon ); // can be const!
    }
    Gia_ManForEachCoId( pGia, iObj, i )
    {
        pObj = Gia_ManObj( pGia, iObj );
        iLit0 = Gia_ObjFaninLit0( pObj, iObj );
        iFon0 = Cba_NtkInsertGiaLit( pNtk, iLit0, vLit2Fon ); // can be const!
        iObjNew = Cba_ObjAlloc( pNtk, CBA_BOX_BUF, 1, 1 );
        Cba_ObjSetFinFon( pNtk, iObjNew, 0, iFon0 );
        iFon0 = Cba_ObjFon0(pNtk, iObjNew); // non-const fon unique for this output
        NameId = pGia->vNamesOut? Abc_NamStrFindOrAdd(p->pStrs, Vec_PtrEntry(pGia->vNamesOut, i), NULL) : Cba_ManNewStrId_(p, "o", i, NULL);
        iObjNew = Cba_ObjAlloc( pNtk, CBA_OBJ_PO, 1, 0 );
        Cba_ObjSetName( pNtk, iObjNew, NameId );
        Cba_ObjSetFinFon( pNtk, iObjNew, 0, iFon0 );
    }
    Cba_NtkCleanFonNames( pNtk );
    Cba_NtkCreateFonNames( pNtk, "a" );
    Vec_IntFree( vLit2Fon );
    return p;
}


/**Function*************************************************************

  Synopsis    [Inserts the network into the root module instead of objects.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_NtkInsertGroup( Cba_Ntk_t * p, Vec_Int_t * vObjs, Cba_Ntk_t * pSyn )
{
    Vec_Int_t * vFonIns  = Cba_NtkCollectInFons( p, vObjs );
    Vec_Int_t * vFonOuts = Cba_NtkCollectOutFons( p, vObjs );
    int k, iObj, iObjNew, iFin, iFon;
    assert( Cba_NtkPiNum(pSyn) == Vec_IntSize(vFonIns) );
    assert( Cba_NtkPoNum(pSyn) == Vec_IntSize(vFonOuts) );
    // mark AIG with the input fons
    Cba_NtkCleanFonCopies( pSyn );
    Cba_NtkForEachPiFon( pSyn, iObj, iFon, k )
        Cba_FonSetCopy( pSyn, iFon, Vec_IntEntry(vFonIns, k) );
    Vec_IntFree( vFonIns );
    // build up internal nodes
    Cba_NtkCleanObjCopies( pSyn );
    Cba_NtkForEachBox( pSyn, iObj )
    {
        iObjNew = Cba_ObjDup( p, pSyn, iObj );
        Cba_ObjForEachFon( pSyn, iObj, iFon, k )
            Cba_FonSetCopy( pSyn, iFon, Cba_ObjFon(p, iObjNew, k) );
    }
    // connect internal nodes
    Cba_NtkForEachBox( pSyn, iObj )
    {
        iObjNew = Cba_ObjCopy( pSyn, iObj );
        Cba_ObjForEachFinFon( pSyn, iObj, iFin, iFon, k )
            Cba_ObjSetFinFon( p, iObjNew, k, Cba_FonCopy(pSyn, iFon) );
    }
    // connect output fons
    Cba_NtkCleanFonCopies( p );
    if ( Cba_NtkHasFonNames(p) )
        Vec_IntFillExtra( &p->vFonName, Cba_NtkFonNum(p) + 1, 0 );
    Cba_NtkForEachPoDriverFon( pSyn, iObj, iFon, k )
    {
        assert( Cba_FonIsReal(Cba_FonCopy(pSyn, iFon)) );
        Cba_FonSetCopy( p, Vec_IntEntry(vFonOuts, k), Cba_FonCopy(pSyn, iFon) );
        // transfer names
        if ( Cba_NtkHasFonNames(p) )
        {
            Cba_FonSetName( p, Cba_FonCopy(pSyn, iFon), Cba_FonName(p, Vec_IntEntry(vFonOuts, k)) );
            Cba_FonCleanName( p, Vec_IntEntry(vFonOuts, k) );
        }
    }
    Vec_IntFree( vFonOuts );
    // delete nodes
//    Vec_IntForEachEntry( vObjs, iObj, k )
//        Cba_ObjDelete( p, iObj );
    // update fins pointing to output fons to point to the new fons
    Cba_NtkForEachFinFon( p, iFon, iFin )
        if ( Cba_FonIsReal(iFon) && Cba_FonCopy(p, iFon) )
            Cba_PatchFinFon( p, iFin, Cba_FonCopy(p, iFon) );
    Cba_NtkMissingFonNames( p, "j" );
/*
    // duplicate in DFS order
    pNew = Cba_NtkDupOrder( p->pDesign, p, Cba_NtkCollectDfs );
    Cba_NtkDupAttrs( pNew, p );
    // replace "p" with "pNew"
    Cba_NtkUpdate( Cba_NtkMan(p), pNew ); // removes "p"
    return pNew;
*/
}
Cba_Man_t * Cba_ManInsertGroup( Cba_Man_t * p, Vec_Int_t * vObjs, Cba_Ntk_t * pSyn )
{
    Cba_NtkInsertGroup( Cba_ManRoot(p), vObjs, pSyn );
    Cba_NtkCheckComboLoop( Cba_ManRoot(p) );
    return Cba_ManDup( p, Cba_NtkCollectDfs );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

