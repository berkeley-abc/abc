/**CFile****************************************************************

  FileName    [wlcNtk.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Verilog parser.]

  Synopsis    [Network data-structure.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 22, 2014.]

  Revision    [$Id: wlcNtk.c,v 1.00 2014/09/12 00:00:00 alanmi Exp $]

***********************************************************************/

#include "wlc.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// object types
static char * Wlc_Names[WLC_OBJ_NUMBER+1] = { 
    NULL,                  // 00: unknown
    "pi",                  // 01: primary input 
    "po",                  // 02: primary output 
    "bo",                  // 03: box output
    "bi",                  // 04: box input
    "ff",                  // 05: flop
    "const",               // 06: constant
    "buf",                 // 07: buffer
    "mux",                 // 08: multiplexer
    ">>",                  // 09: shift right
    ">>>",                 // 10: shift right (arithmetic)
    "<<",                  // 11: shift left
    "<<<",                 // 12: shift left (arithmetic)
    "~",                   // 13: bitwise NOT
    "&",                   // 14: bitwise AND
    "|",                   // 15: bitwise OR
    "^",                   // 16: bitwise XOR
    "[:]",                 // 17: bit selection
    "{,}",                 // 18: bit concatenation
    "BitPad",              // 19: zero padding
    "SgnExt",              // 20: sign extension
    "!",                   // 21: logic NOT
    "&&",                  // 22: logic AND
    "||",                  // 23: logic OR
    "==",                  // 24: compare equal
    "!=",                  // 25: compare not equal
    "<",                   // 26: compare less
    ">",                   // 27: compare more
    "<=",                  // 28: compare less or equal
    ">=",                  // 29: compare more or equal
    "&",                   // 30: reduction AND
    "|",                   // 31: reduction OR
    "^",                   // 32: reduction XOR
    "+",                   // 33: arithmetic addition
    "-",                   // 34: arithmetic subtraction
    "*",                   // 35: arithmetic multiplier
    "//",                  // 36: arithmetic division
    "%%",                  // 37: arithmetic modulus
    "**",                  // 38: arithmetic power
    "table",               // 39: lookup table
    NULL                   // 40: unused
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Working with models.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Wlc_Ntk_t * Wlc_NtkAlloc( char * pName, int nObjsAlloc )
{
    Wlc_Ntk_t * p;
    p = ABC_CALLOC( Wlc_Ntk_t, 1 );
    p->pName = Extra_FileNameGeneric( pName );
    Vec_IntGrow( &p->vPis, 111 );
    Vec_IntGrow( &p->vPos, 111 );
    Vec_IntGrow( &p->vCis, 111 );
    Vec_IntGrow( &p->vCos, 111 );
    Vec_IntGrow( &p->vFfs, 111 );
    p->pMemFanin = Mem_FlexStart();
    p->nObjsAlloc = nObjsAlloc;  
    p->pObjs = ABC_CALLOC( Wlc_Obj_t, p->nObjsAlloc );
    p->iObj = 1;
    return p;
}
int Wlc_ObjAlloc( Wlc_Ntk_t * p, int Type, int Signed, int End, int Beg )
{
    Wlc_Obj_t * pObj;
    if ( p->iObj == p->nObjsAlloc )
    {
        p->pObjs = ABC_REALLOC( Wlc_Obj_t, p->pObjs, 2 * p->nObjsAlloc );
        memset( p->pObjs + p->nObjsAlloc, 0, sizeof(Wlc_Obj_t) * p->nObjsAlloc );
        p->nObjsAlloc *= 2;
    }
    pObj = Wlc_NtkObj( p, p->iObj );
    pObj->Type   = Type;
    pObj->Signed = Signed;
    pObj->End    = End;
    pObj->Beg    = Beg;
    if ( Type == WLC_OBJ_PI )
    {
        pObj->Fanins[1] = Vec_IntSize(&p->vPis);
        Vec_IntPush( &p->vPis, p->iObj );
    }
    else if ( Type == WLC_OBJ_PO )
    {
        pObj->Fanins[1] = Vec_IntSize(&p->vPos);
        Vec_IntPush( &p->vPos, p->iObj );
    }
    p->nObjs[Type]++;
    return p->iObj++;
}
char * Wlc_ObjName( Wlc_Ntk_t * p, int iObj )
{
    static char Buffer[100];
    if ( Wlc_NtkHasNameId(p) && Wlc_ObjNameId(p, iObj) )
        return Abc_NamStr( p->pManName, Wlc_ObjNameId(p, iObj) );
    sprintf( Buffer, "n%d", iObj );
    return Buffer;
}                          
void Wlc_ObjUpdateType( Wlc_Ntk_t * p, Wlc_Obj_t * pObj, int Type )
{
    if ( pObj->Type == WLC_OBJ_PO )
    {
        assert( Type == WLC_OBJ_BUF );
        return;
    }
    p->nObjs[pObj->Type]--;
    pObj->Type = Type;
    p->nObjs[pObj->Type]++;
}
void Wlc_ObjAddFanins( Wlc_Ntk_t * p, Wlc_Obj_t * pObj, Vec_Int_t * vFanins )
{
    assert( pObj->nFanins == 0 );
    pObj->nFanins = Vec_IntSize(vFanins);
    if ( Wlc_ObjHasArray(pObj) )
        pObj->pFanins[0] = (int *)Mem_FlexEntryFetch( p->pMemFanin, Vec_IntSize(vFanins) * sizeof(int) );
    memcpy( Wlc_ObjFanins(pObj), Vec_IntArray(vFanins), sizeof(int) * Vec_IntSize(vFanins) );
    // special treatment of CONST, SELECT and TABLE
    if ( pObj->Type == WLC_OBJ_CONST )
        pObj->nFanins = 0;
    else if ( pObj->Type == WLC_OBJ_BIT_SELECT || pObj->Type == WLC_OBJ_TABLE )
        pObj->nFanins = 1;
}
void Wlc_NtkFree( Wlc_Ntk_t * p )
{
    if ( p->pManName )
        Abc_NamStop( p->pManName );
    if ( p->pMemFanin )
        Mem_FlexStop( p->pMemFanin, 0 );
    if ( p->pMemTable )
        Mem_FlexStop( p->pMemTable, 0 );
    Vec_PtrFreeP( &p->vTables );
    ABC_FREE( p->vPis.pArray );
    ABC_FREE( p->vPos.pArray );
    ABC_FREE( p->vCis.pArray );
    ABC_FREE( p->vCos.pArray );
    ABC_FREE( p->vFfs.pArray );
    ABC_FREE( p->vTravIds.pArray );
    ABC_FREE( p->vNameIds.pArray );
    ABC_FREE( p->vCopies.pArray );
    ABC_FREE( p->pObjs );
    ABC_FREE( p->pName );
    ABC_FREE( p );
}
int Wlc_NtkMemUsage( Wlc_Ntk_t * p )
{
    int Mem = sizeof(Wlc_Ntk_t);
    Mem += 4 * p->vPis.nCap;
    Mem += 4 * p->vPos.nCap;
    Mem += 4 * p->vCis.nCap;
    Mem += 4 * p->vCos.nCap;
    Mem += 4 * p->vFfs.nCap;
    Mem += sizeof(Wlc_Obj_t) * p->nObjsAlloc;
    Mem += Abc_NamMemUsed(p->pManName);
    Mem += Mem_FlexReadMemUsage(p->pMemFanin);
    return Mem;
}
void Wlc_NtkPrintNodes( Wlc_Ntk_t * p, int Type )
{
    Wlc_Obj_t * pObj; 
    int i, Counter = 0;
    printf( "Operation %s\n", Wlc_Names[Type] );
    Wlc_NtkForEachObj( p, pObj, i )
    {
        if ( (int)pObj->Type != Type )
            continue;
        printf( "%8d  :",      Counter++ );
        printf( "%8d  :  ",    i );
        printf( "%3d%s = ",    Wlc_ObjRange(pObj),                   pObj->Signed ? "s" : " " );
        printf( "%3d%s  %s ",  Wlc_ObjRange(Wlc_ObjFanin0(p, pObj)), Wlc_ObjFanin0(p, pObj)->Signed ? "s" : " ", Wlc_Names[Type] );
        printf( "%3d%s ",      Wlc_ObjRange(Wlc_ObjFanin1(p, pObj)), Wlc_ObjFanin1(p, pObj)->Signed ? "s" : " " );
        printf( " :    " );
        printf( "%-12s =  ",   Wlc_ObjName(p, i) );
        printf( "%-12s  %s  ", Wlc_ObjName(p, Wlc_ObjFaninId0(pObj)), Wlc_Names[Type] );
        printf( "%-12s ",      Wlc_ObjName(p, Wlc_ObjFaninId1(pObj)) );
        printf( "\n" );
    }
}
void Wlc_NtkPrintStats( Wlc_Ntk_t * p, int fVerbose )
{
    int i;
    printf( "%-20s : ",        p->pName );
    printf( "PI = %4d  ",      Wlc_NtkPiNum(p) );
    printf( "PO = %4d  ",      Wlc_NtkPoNum(p) );
    printf( "FF = %4d  ",      Wlc_NtkFfNum(p) );
    printf( "Obj = %6d  ",     Wlc_NtkObjNum(p) );
    printf( "Mem = %.3f MB",   1.0*Wlc_NtkMemUsage(p)/(1<<20) );
    printf( "\n" );
    if ( !fVerbose )
        return;
    printf( "Node type statisticts:\n" );
    for ( i = 0; i < WLC_OBJ_NUMBER; i++ )
        if ( p->nObjs[i] )
            printf( "%2d  :  %6d  %-8s\n", i, p->nObjs[i], Wlc_Names[i] );
//    Wlc_NtkPrintNodes( p, WLC_OBJ_ARI_MULTI );
}

/**Function*************************************************************

  Synopsis    [Duplicates the network in a topological order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Wlc_ObjCollectCopyFanins( Wlc_Ntk_t * p, int iObj, Vec_Int_t * vFanins )
{
    int i, iFanin;
    Wlc_Obj_t * pObj = Wlc_NtkObj( p, iObj );
    Vec_IntClear( vFanins );
    Wlc_ObjForEachFanin( pObj, iFanin, i )
        Vec_IntPush( vFanins, Wlc_ObjCopy(p, iFanin) );
    // special treatment of CONST and SELECT
    if ( pObj->Type == WLC_OBJ_CONST )
    {
        int * pInts = Wlc_ObjConstValue( pObj );
        int nInts = Abc_BitWordNum( Wlc_ObjRange(pObj) );
        for ( i = 0; i < nInts; i++ )
            Vec_IntPush( vFanins, pInts[i] );
    }
    else if ( pObj->Type == WLC_OBJ_BIT_SELECT || pObj->Type == WLC_OBJ_TABLE )
    {
        assert( Vec_IntSize(vFanins) == 1 );
        Vec_IntPush( vFanins, pObj->Fanins[1] );
    }
}
int Wlc_ObjDup( Wlc_Ntk_t * pNew, Wlc_Ntk_t * p, int iObj, Vec_Int_t * vFanins )
{
    Wlc_Obj_t * pObj = Wlc_NtkObj( p, iObj );
    int iFaninNew = Wlc_ObjAlloc( pNew, pObj->Type, pObj->Signed, pObj->End, pObj->Beg );
    Wlc_Obj_t * pObjNew = Wlc_NtkObj(pNew, iFaninNew);
    Wlc_ObjCollectCopyFanins( p, iObj, vFanins );
    Wlc_ObjAddFanins( pNew, pObjNew, vFanins );
    Wlc_ObjSetCopy( p, iObj, iFaninNew );
    return iFaninNew;
}
void Wlc_NtkDupDfs_rec( Wlc_Ntk_t * pNew, Wlc_Ntk_t * p, int iObj, Vec_Int_t * vFanins )
{
    Wlc_Obj_t * pObj;
    int i, iFanin;
    if ( Wlc_ObjCopy(p, iObj) )
        return;
    pObj = Wlc_NtkObj( p, iObj );
    Wlc_ObjForEachFanin( pObj, iFanin, i )
        Wlc_NtkDupDfs_rec( pNew, p, iFanin, vFanins );
    Wlc_ObjDup( pNew, p, iObj, vFanins );
}
Wlc_Ntk_t * Wlc_NtkDupDfs( Wlc_Ntk_t * p )
{
    Wlc_Ntk_t * pNew;
    Wlc_Obj_t * pObj;
    Vec_Int_t * vFanins;
    int i;
    Wlc_NtkCleanCopy( p );
    vFanins = Vec_IntAlloc( 100 );
    pNew = Wlc_NtkAlloc( p->pName, p->nObjsAlloc );
    Wlc_NtkForEachPi( p, pObj, i )
        Wlc_ObjDup( pNew, p, Wlc_ObjId(p, pObj), vFanins );
    Wlc_NtkForEachPo( p, pObj, i )
        Wlc_NtkDupDfs_rec( pNew, p, Wlc_ObjFaninId0(pObj), vFanins );
    Wlc_NtkForEachPo( p, pObj, i )
        Wlc_ObjDup( pNew, p, Wlc_ObjId(p, pObj), vFanins );
    Vec_IntFree( vFanins );
    return pNew;
}
void Wlc_NtkTransferNames( Wlc_Ntk_t * pNew, Wlc_Ntk_t * p )
{
    int i;
    assert( !Wlc_NtkHasCopy(pNew)   && Wlc_NtkHasCopy(p)   );
    assert( !Wlc_NtkHasNameId(pNew) && Wlc_NtkHasNameId(p) );
    assert( pNew->pManName  == NULL && p->pManName != NULL );
    Wlc_NtkCleanNameId( pNew );
    for ( i = 0; i < p->nObjsAlloc; i++ )
        if ( Wlc_ObjCopy(p, i) && Wlc_ObjNameId(p, i) )
            Wlc_ObjSetNameId( pNew, Wlc_ObjCopy(p, i), Wlc_ObjNameId(p, i) );
    pNew->pManName = p->pManName; 
    p->pManName = NULL;
    Vec_IntErase( &p->vNameIds );
    // transfer table
    pNew->pMemTable = p->pMemTable;  p->pMemTable = NULL;
    pNew->vTables = p->vTables;      p->vTables = NULL;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

