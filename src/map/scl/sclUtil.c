/**CFile****************************************************************

  FileName    [sclUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  Synopsis    [Standard-cell library representation.]

  Author      [Alan Mishchenko, Niklas Een]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 24, 2012.]

  Revision    [$Id: sclUtil.c,v 1.0 2012/08/24 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sclInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////


/**Function*************************************************************

  Synopsis    [Reading library from file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static unsigned Abc_SclHashString( char * pName, int TableSize ) 
{
    static int s_Primes[10] = { 1291, 1699, 2357, 4177, 5147, 5647, 6343, 7103, 7873, 8147 };
    unsigned i, Key = 0;
    for ( i = 0; pName[i] != '\0'; i++ )
        Key += s_Primes[i%10]*pName[i]*pName[i];
    return Key % TableSize;
}
int * Abc_SclHashLookup( SC_Lib * p, char * pName )
{
    int i;
    for ( i = Abc_SclHashString(pName, p->nBins); i < p->nBins; i = (i + 1) % p->nBins )
        if ( p->pBins[i] == -1 || !strcmp(pName, SC_LibCell(p, p->pBins[i])->name) )
            return p->pBins + i;
    assert( 0 );
    return NULL;
}
void Abc_SclHashCells( SC_Lib * p )
{
    SC_Cell * pCell;
    int i, * pPlace;
    assert( p->nBins == 0 );
    p->nBins = Abc_PrimeCudd( 5 * Vec_PtrSize(p->vCells) );
    p->pBins = ABC_FALLOC( int, p->nBins );
    SC_LitForEachCell( p, pCell, i )
    {
        pPlace = Abc_SclHashLookup( p, pCell->name );
        assert( *pPlace == -1 );
        *pPlace = i;
    }
}
int Abc_SclCellFind( SC_Lib * p, char * pName )
{
    return *Abc_SclHashLookup( p, pName );
}

/**Function*************************************************************

  Synopsis    [Links equal gates into rings while sorting them by area.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Abc_SclCompareCells( SC_Cell ** pp1, SC_Cell ** pp2 )
{
    if ( (*pp1)->n_inputs < (*pp2)->n_inputs )
        return -1;
    if ( (*pp1)->n_inputs > (*pp2)->n_inputs )
        return 1;
    if ( (*pp1)->area < (*pp2)->area )
        return -1;
    if ( (*pp1)->area > (*pp2)->area )
        return 1;
    return strcmp( (*pp1)->name, (*pp2)->name );
}
void Abc_SclLinkCells( SC_Lib * p )
{
    SC_Cell * pCell, * pRepr;
    int i, k;
    assert( Vec_PtrSize(p->vCellOrder) == 0 );
    SC_LitForEachCell( p, pCell, i )
    {
        // find gate with the same function
        Vec_PtrForEachEntry( SC_Cell *, p->vCellOrder, pRepr, k )
            if ( pCell->n_inputs  == pRepr->n_inputs && 
                 pCell->n_outputs == pRepr->n_outputs && 
                 Vec_WrdEqual(SC_CellFunc(pCell), SC_CellFunc(pRepr)) )
                break;
        if ( k == Vec_PtrSize(p->vCellOrder) )
        {
            Vec_PtrPush( p->vCellOrder, pCell );
            pCell->pNext = pCell->pPrev = pCell;
            continue;
        }
        // add it to the list before the cell
        pRepr->pPrev->pNext = pCell; pCell->pNext = pRepr;
        pCell->pPrev = pRepr->pPrev; pRepr->pPrev = pCell;
    }
    // sort cells by size the then by name
    qsort( (void *)Vec_PtrArray(p->vCellOrder), Vec_PtrSize(p->vCellOrder), sizeof(void *), (int(*)(const void *,const void *))Abc_SclCompareCells );
    // sort cell lists
    Vec_PtrForEachEntry( SC_Cell *, p->vCellOrder, pRepr, k )
    {
        Vec_Ptr_t * vList = Vec_PtrAlloc( 100 );
        SC_RingForEachCell( pRepr, pCell, i )
            Vec_PtrPush( vList, pCell );
        qsort( (void *)Vec_PtrArray(vList), Vec_PtrSize(vList), sizeof(void *), (int(*)(const void *,const void *))Abc_SclCompareCells );
        // create new representative
        pRepr = Vec_PtrEntry( vList, 0 );
        pRepr->pNext = pRepr->pPrev = pRepr;
        // relink cells
        Vec_PtrForEachEntryStart( SC_Cell *, vList, pCell, i, 1 )
        {
            pRepr->pPrev->pNext = pCell; pCell->pNext = pRepr;
            pCell->pPrev = pRepr->pPrev; pRepr->pPrev = pCell;
        }
        // update list
        Vec_PtrWriteEntry( p->vCellOrder, k, pRepr );
        Vec_PtrFree( vList );
    }
}
void Abc_SclPrintCells( SC_Lib * p )
{
    extern void Kit_DsdPrintFromTruth( unsigned * pTruth, int nVars );
    SC_Cell * pCell, * pRepr;
    int i, k;
    assert( Vec_PtrSize(p->vCellOrder) > 0 );
    printf( "Library \"%s\" ", p->lib_name );
    printf( "containing %d cells in %d classes.\n", 
        Vec_PtrSize(p->vCells), Vec_PtrSize(p->vCellOrder) );
    Vec_PtrForEachEntry( SC_Cell *, p->vCellOrder, pRepr, k )
    {
        printf( "Class%3d : ", k );
        printf( "Ins = %d  ",  pRepr->n_inputs );
        printf( "Outs = %d", pRepr->n_outputs );
        for ( i = 0; i < pRepr->n_outputs; i++ )
        {
            printf( "   "  );
            Kit_DsdPrintFromTruth( (unsigned *)Vec_WrdArray(SC_CellPin(pRepr, pRepr->n_inputs+i)->vFunc), pRepr->n_inputs );
        }
        printf( "\n" );
        SC_RingForEachCell( pRepr, pCell, i )
        {
            printf( "           %3d : ",  i+1 );
            printf( "%-12s  ",            pCell->name );
            printf( "%2d   ",             pCell->drive_strength );
            printf( "A =%8.3f",           pCell->area );
            printf( "\n" );
        }
    }
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

