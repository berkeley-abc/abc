/**CFile****************************************************************

  FileName    [giaAigerExt.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Scalable AIG package.]

  Synopsis    [Custom AIGER extensions.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: giaAigerExt.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "gia.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Read/write equivalence classes information.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
Gia_Rpr_t * Gia_AigerReadEquivClasses( unsigned char ** ppPos, int nSize )
{
    Gia_Rpr_t * pReprs;
    unsigned char * pStop;
    int i, Item, fProved, iRepr, iNode;
    pStop = *ppPos;
    pStop += Gia_AigerReadInt( *ppPos ); *ppPos += 4;
    pReprs = ABC_CALLOC( Gia_Rpr_t, nSize );
    for ( i = 0; i < nSize; i++ )
        pReprs[i].iRepr = GIA_VOID;
    iRepr = iNode = 0;
    while ( *ppPos < pStop )
    {
        Item = Gia_AigerReadUnsigned( ppPos );
        if ( Item & 1 )
        {
            iRepr += (Item >> 1);
            iNode = iRepr;
            continue;
        }
        Item >>= 1;
        fProved = (Item & 1);
        Item >>= 1;
        iNode += Item;
        pReprs[iNode].fProved = fProved;
        pReprs[iNode].iRepr = iRepr;
        assert( iRepr < iNode );
    }
    return pReprs;
}
unsigned char * Gia_WriteEquivClassesInt( Gia_Man_t * p, int * pEquivSize )
{
    unsigned char * pBuffer;
    int iRepr, iNode, iPrevRepr, iPrevNode, iLit, nItems, iPos;
    assert( p->pReprs && p->pNexts );
    // count the number of entries to be written
    nItems = 0;
    for ( iRepr = 1; iRepr < Gia_ManObjNum(p); iRepr++ )
    {
        nItems += Gia_ObjIsConst( p, iRepr );
        if ( !Gia_ObjIsHead(p, iRepr) )
            continue;
        Gia_ClassForEachObj( p, iRepr, iNode )
            nItems++;
    }
    pBuffer = ABC_ALLOC( unsigned char, sizeof(int) * (nItems + 10) );
    // write constant class
    iPos = Gia_AigerWriteUnsignedBuffer( pBuffer, 4, Abc_Var2Lit(0, 1) );
    iPrevNode = 0;
    for ( iNode = 1; iNode < Gia_ManObjNum(p); iNode++ )
        if ( Gia_ObjIsConst(p, iNode) )
        {
            iLit = Abc_Var2Lit( iNode - iPrevNode, Gia_ObjProved(p, iNode) );
            iPrevNode = iNode;
            iPos = Gia_AigerWriteUnsignedBuffer( pBuffer, iPos, Abc_Var2Lit(iLit, 0) );
        }
    // write non-constant classes
    iPrevRepr = 0;
    Gia_ManForEachClass( p, iRepr )
    {
        iPos = Gia_AigerWriteUnsignedBuffer( pBuffer, iPos, Abc_Var2Lit(iRepr - iPrevRepr, 1) );
        iPrevRepr = iPrevNode = iRepr;
        Gia_ClassForEachObj1( p, iRepr, iNode )
        {
            iLit = Abc_Var2Lit( iNode - iPrevNode, Gia_ObjProved(p, iNode) );
            iPrevNode = iNode;
            iPos = Gia_AigerWriteUnsignedBuffer( pBuffer, iPos, Abc_Var2Lit(iLit, 0) );
        }
    }
    Gia_AigerWriteInt( pBuffer, iPos );
    *pEquivSize = iPos;
    return pBuffer;
}
Vec_Str_t * Gia_WriteEquivClasses( Gia_Man_t * p )
{
    int nEquivSize;
    unsigned char * pBuffer = Gia_WriteEquivClassesInt( p, &nEquivSize );
    return Vec_StrAllocArray( (char *)pBuffer, nEquivSize );
}

/**Function*************************************************************

  Synopsis    [Read/write mapping information.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline unsigned Gia_AigerReadDiffValue( unsigned char ** ppPos, int iPrev )
{
    int Item = Gia_AigerReadUnsigned( ppPos );
    if ( Item & 1 )
        return iPrev + (Item >> 1);
    return iPrev - (Item >> 1);
}
int * Gia_AigerReadMapping( unsigned char ** ppPos, int nSize )
{
    int * pMapping;
    unsigned char * pStop;
    int k, j, nFanins, nAlloc, iNode = 0, iOffset = nSize;
    pStop = *ppPos;
    pStop += Gia_AigerReadInt( *ppPos ); *ppPos += 4;
    nAlloc = nSize + pStop - *ppPos;
    pMapping = ABC_CALLOC( int, nAlloc );
    while ( *ppPos < pStop )
    {
        k = iOffset;
        pMapping[k++] = nFanins = Gia_AigerReadUnsigned( ppPos );
        for ( j = 0; j <= nFanins; j++ )
            pMapping[k++] = iNode = Gia_AigerReadDiffValue( ppPos, iNode );
        pMapping[iNode] = iOffset;
        iOffset = k;
    }
    assert( iOffset <= nAlloc );
    return pMapping;
}
static inline int Gia_AigerWriteDiffValue( unsigned char * pPos, int iPos, int iPrev, int iThis )
{
    if ( iPrev < iThis )
        return Gia_AigerWriteUnsignedBuffer( pPos, iPos, Abc_Var2Lit(iThis - iPrev, 1) );
    return Gia_AigerWriteUnsignedBuffer( pPos, iPos, Abc_Var2Lit(iPrev - iThis, 0) );
}
unsigned char * Gia_AigerWriteMappingInt( Gia_Man_t * p, int * pMapSize )
{
    unsigned char * pBuffer;
    int i, k, iPrev, iFan, nItems, iPos = 4;
    assert( p->pMapping );
    // count the number of entries to be written
    nItems = 0;
    Gia_ManForEachLut( p, i )
        nItems += 2 + Gia_ObjLutSize( p, i );
    pBuffer = ABC_ALLOC( unsigned char, sizeof(int) * (nItems + 1) );
    // write non-constant classes
    iPrev = 0;
    Gia_ManForEachLut( p, i )
    {
//printf( "\nSize = %d ", Gia_ObjLutSize(p, i) );
        iPos = Gia_AigerWriteUnsignedBuffer( pBuffer, iPos, Gia_ObjLutSize(p, i) );
        Gia_LutForEachFanin( p, i, iFan, k )
        {
//printf( "Fan = %d ", iFan );
            iPos = Gia_AigerWriteDiffValue( pBuffer, iPos, iPrev, iFan );
            iPrev = iFan;
        }
        iPos = Gia_AigerWriteDiffValue( pBuffer, iPos, iPrev, i );
        iPrev = i;
//printf( "Node = %d ", i );
    }
//printf( "\n" );
    Gia_AigerWriteInt( pBuffer, iPos );
    *pMapSize = iPos;
    return pBuffer;
}
Vec_Str_t * Gia_AigerWriteMapping( Gia_Man_t * p )
{
    int nMapSize;
    unsigned char * pBuffer = Gia_AigerWriteMappingInt( p, &nMapSize );
    return Vec_StrAllocArray( (char *)pBuffer, nMapSize );
}

/**Function*************************************************************

  Synopsis    [Read/write mapping information.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
int * Gia_AigerReadMappingSimple( unsigned char ** ppPos, int nSize )
{
    int * pMapping = ABC_ALLOC( int, nSize/4 );
    memcpy( pMapping, *ppPos, nSize );
    assert( nSize % 4 == 0 );
    return pMapping;
}
Vec_Str_t * Gia_AigerWriteMappingSimple( Gia_Man_t * p )
{
    unsigned char * pBuffer = ABC_ALLOC( unsigned char, 4*p->nOffset );
    memcpy( pBuffer, p->pMapping, 4*p->nOffset );
    assert( p->pMapping != NULL && p->nOffset >= Gia_ManObjNum(p) );
    return Vec_StrAllocArray( (char *)pBuffer, 4*p->nOffset );
}

/**Function*************************************************************

  Synopsis    [Read/write packing information.]

  Description []
  
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Gia_AigerReadPacking( unsigned char ** ppPos, int nSize )
{
    Vec_Int_t * vPacking = Vec_IntStart( nSize/4 );
    assert( nSize % 4 == 0 );
    memcpy( Vec_IntArray(vPacking), *ppPos, nSize );
    *ppPos += nSize;
    return vPacking;
}
Vec_Str_t * Gia_WritePacking( Vec_Int_t * vPacking )
{
    Vec_Str_t * vBuffer = Vec_StrStart( 4*Vec_IntSize(vPacking) );
    memcpy( Vec_StrArray(vBuffer), Vec_IntArray(vPacking), 4*Vec_IntSize(vPacking) );
    return vBuffer;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

