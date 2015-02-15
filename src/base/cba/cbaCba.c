/**CFile****************************************************************

  FileName    [cbaCba.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Hierarchical word-level netlist.]

  Synopsis    [Verilog parser.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - November 29, 2014.]

  Revision    [$Id: cbaCba.c,v 1.00 2014/11/29 00:00:00 alanmi Exp $]

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

  Synopsis    [Read CBA.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int CbaManReadCbaLine( Vec_Str_t * vOut, int * pPos, char * pBuffer, char * pLimit )
{
    char c;
    while ( (c = Vec_StrEntry(vOut, (*pPos)++)) != '\n' && pBuffer < pLimit )
        *pBuffer++ = c;
    *pBuffer = 0;
    return pBuffer < pLimit;
}
int CbaManReadCbaNameAndNums( char * pBuffer, int * Num1, int * Num2, int * Num3, int * Num4 )
{
    *Num1 = *Num2 = *Num3 = *Num4 = -1;
    // read name
    while ( *pBuffer && *pBuffer != ' ' )
        pBuffer++;
    if ( !*pBuffer )
        return 0;
    assert( *pBuffer == ' ' );
    *pBuffer = 0;
    // read Num1
    *Num1 = atoi(++pBuffer);
    while ( *pBuffer && *pBuffer != ' ' )
        pBuffer++;
    if ( !*pBuffer )
        return 0;
    // read Num2
    assert( *pBuffer == ' ' );
    *Num2 = atoi(++pBuffer);
    while ( *pBuffer && *pBuffer != ' ' )
        pBuffer++;
    if ( !*pBuffer )
        return 1;
    // read Num3
    assert( *pBuffer == ' ' );
    *Num3 = atoi(++pBuffer);
    while ( *pBuffer && *pBuffer != ' ' )
        pBuffer++;
    if ( !*pBuffer )
        return 1;
    // read Num4
    assert( *pBuffer == ' ' );
    *Num4 = atoi(++pBuffer);
    return 1;
}
void Cba_ManReadCbaVecStr( Vec_Str_t * vOut, int * pPos, Vec_Str_t * p, int nSize )
{
    memcpy( Vec_StrArray(p), Vec_StrArray(vOut) + *pPos, nSize );
    *pPos += nSize;
    p->nSize = nSize;
    assert( Vec_StrSize(p) == Vec_StrCap(p) );
}
void Cba_ManReadCbaVecInt( Vec_Str_t * vOut, int * pPos, Vec_Int_t * p, int nSize )
{
    memcpy( Vec_IntArray(p), Vec_StrArray(vOut) + *pPos, nSize );
    *pPos += nSize;
    p->nSize = nSize / 4;
    assert( Vec_IntSize(p) == Vec_IntCap(p) );
}
void Cba_ManReadCbaNtk( Vec_Str_t * vOut, int * pPos, Cba_Ntk_t * pNtk )
{
    int i, Type;
    Cba_ManReadCbaVecStr( vOut, pPos, &pNtk->vType,      Cba_NtkObjNumAlloc(pNtk) );
    Cba_ManReadCbaVecInt( vOut, pPos, &pNtk->vFanin, 4 * Cba_NtkObjNumAlloc(pNtk) );
    Cba_ManReadCbaVecInt( vOut, pPos, &pNtk->vInfo, 12 * Cba_NtkInfoNumAlloc(pNtk) );
    Cba_NtkForEachObjType( pNtk, Type, i )
    {
        if ( Type == CBA_OBJ_PI )
            Vec_IntPush( &pNtk->vInputs, i );
        if ( Type == CBA_OBJ_PO )
            Vec_IntPush( &pNtk->vOutputs, i );
    }
    assert( Cba_NtkPiNum(pNtk)  == Cba_NtkPiNumAlloc(pNtk) );
    assert( Cba_NtkPoNum(pNtk)  == Cba_NtkPoNumAlloc(pNtk) );
    assert( Cba_NtkObjNum(pNtk) == Cba_NtkObjNumAlloc(pNtk) );
    assert( Cba_NtkInfoNum(pNtk) == Cba_NtkInfoNumAlloc(pNtk) );
}
Cba_Man_t * Cba_ManReadCbaInt( Vec_Str_t * vOut )
{
    Cba_Man_t * p;
    Cba_Ntk_t * pNtk;
    char Buffer[1000] = "#"; 
    int i, NameId, Pos = 0, nNtks, nPrims, Num1, Num2, Num3, Num4;
    while ( Buffer[0] == '#' )
        if ( !CbaManReadCbaLine(vOut, &Pos, Buffer, Buffer+1000) )
            return NULL;
    if ( !CbaManReadCbaNameAndNums(Buffer, &nNtks, &nPrims, &Num3, &Num4) )
        return NULL;
    // start manager
    assert( nNtks > 0 && nPrims > 0 );
    p = Cba_ManAlloc( Buffer, nNtks );
    // start networks
    Cba_ManForEachNtk( p, pNtk, i )
    {
        if ( !CbaManReadCbaLine(vOut, &Pos, Buffer, Buffer+1000) )
        {
            Cba_ManFree( p );
            return NULL;
        }
        if ( !CbaManReadCbaNameAndNums(Buffer, &Num1, &Num2, &Num3, &Num4) )
        {
            Cba_ManFree( p );
            return NULL;
        }
        assert( Num1 > 0 && Num2 > 0 && Num3 > 0 );
        NameId = Abc_NamStrFindOrAdd( p->pStrs, Buffer, NULL );
        Cba_NtkAlloc( pNtk, NameId, Num1, Num2, Num3 );
        Vec_IntFill( &pNtk->vInfo, 3 * Num4, -1 );
    }
    // read networks
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_ManReadCbaNtk( vOut, &Pos, pNtk );
    // read primitives
    for ( i = 0; i < nPrims; i++ )
    {
        char * pName = Vec_StrEntryP( vOut, Pos );     
        Abc_NamStrFindOrAdd( p->pMods, pName, NULL );
        Pos += strlen(pName) + 1;
    }
    assert( Pos == Vec_StrSize(vOut) );
    assert( Cba_ManNtkNum(p) == nNtks );
    assert( Cba_ManPrimNum(p) == nPrims );
    return p;
}
Cba_Man_t * Cba_ManReadCba( char * pFileName )
{
    Cba_Man_t * p;
    FILE * pFile;
    Vec_Str_t * vOut;
    int nFileSize;
    pFile = fopen( pFileName, "rb" );
    if ( pFile == NULL )
    {
        printf( "Cannot open file \"%s\" for reading.\n", pFileName );
        return NULL;
    }
    // get the file size, in bytes
    fseek( pFile, 0, SEEK_END );  
    nFileSize = ftell( pFile );  
    rewind( pFile ); 
    // load the contents
    vOut = Vec_StrAlloc( nFileSize );
    vOut->nSize = vOut->nCap;
    assert( nFileSize == Vec_StrSize(vOut) );
    nFileSize = fread( Vec_StrArray(vOut), 1, Vec_StrSize(vOut), pFile );
    assert( nFileSize == Vec_StrSize(vOut) );
    fclose( pFile );
    // read the library
    p = Cba_ManReadCbaInt( vOut );
    if ( p != NULL )
    {
        ABC_FREE( p->pSpec );
        p->pSpec = Abc_UtilStrsav( pFileName );
    }
    Vec_StrFree( vOut );
    return p;
}

/**Function*************************************************************

  Synopsis    [Write CBA.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cba_ManWriteCbaNtk( Vec_Str_t * vOut, Cba_Ntk_t * pNtk )
{
    Vec_StrPushBuffer( vOut, (char *)Vec_StrArray(&pNtk->vType),       Cba_NtkObjNum(pNtk) );
    Vec_StrPushBuffer( vOut, (char *)Vec_IntArray(&pNtk->vFanin),  4 * Cba_NtkObjNum(pNtk) );
    Vec_StrPushBuffer( vOut, (char *)Vec_IntArray(&pNtk->vInfo),  12 * Cba_NtkInfoNum(pNtk) );
}
void Cba_ManWriteCbaInt( Vec_Str_t * vOut, Cba_Man_t * p )
{
    char Buffer[1000];
    Cba_Ntk_t * pNtk; int i, nPrims = Cba_ManPrimNum(p);
    sprintf( Buffer, "# Design \"%s\" written by ABC on %s\n", Cba_ManName(p), Extra_TimeStamp() );
    Vec_StrPrintStr( vOut, Buffer );
    // write short info
    sprintf( Buffer, "%s %d %d \n", Cba_ManName(p), Cba_ManNtkNum(p), Cba_ManPrimNum(p) );
    Vec_StrPrintStr( vOut, Buffer );
    Cba_ManForEachNtk( p, pNtk, i )
    {
        sprintf( Buffer, "%s %d %d %d %d \n", Cba_NtkName(pNtk), 
            Cba_NtkPiNum(pNtk), Cba_NtkPoNum(pNtk), Cba_NtkObjNum(pNtk), Cba_NtkInfoNum(pNtk) );
        Vec_StrPrintStr( vOut, Buffer );
    }
    Cba_ManForEachNtk( p, pNtk, i )
        Cba_ManWriteCbaNtk( vOut, pNtk );
    for ( i = 0; i < nPrims; i++ )
    {
        char * pName = Abc_NamStr( p->pMods, Cba_ManNtkNum(p) + i );
        Vec_StrPrintStr( vOut, pName );
        Vec_StrPush( vOut, '\0' );
    }
}
void Cba_ManWriteCba( char * pFileName, Cba_Man_t * p )
{
    Vec_Str_t * vOut;
    assert( p->pMioLib == NULL );
    vOut = Vec_StrAlloc( 10000 );
    Cba_ManWriteCbaInt( vOut, p );
    if ( Vec_StrSize(vOut) > 0 )
    {
        FILE * pFile = fopen( pFileName, "wb" );
        if ( pFile == NULL )
            printf( "Cannot open file \"%s\" for writing.\n", pFileName );
        else
        {
            fwrite( Vec_StrArray(vOut), 1, Vec_StrSize(vOut), pFile );
            fclose( pFile );
        }
    }
    Vec_StrFree( vOut );    
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

