/**CFile****************************************************************

  FileName    [sclUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Standard-cell library representation.]

  Synopsis    [Various utilities.]

  Author      [Alan Mishchenko, Niklas Een]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 24, 2012.]

  Revision    [$Id: sclUtil.c,v 1.0 2012/08/24 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sclInt.h"
#include "map/mio/mio.h"
#include "bool/kit/kit.h"

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
        if ( p->pBins[i] == -1 || !strcmp(pName, SC_LibCell(p, p->pBins[i])->pName) )
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
    SC_LibForEachCell( p, pCell, i )
    {
        pPlace = Abc_SclHashLookup( p, pCell->pName );
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
    return strcmp( (*pp1)->pName, (*pp2)->pName );
}
void Abc_SclLinkCells( SC_Lib * p )
{
    SC_Cell * pCell, * pRepr = NULL;
    int i, k;
    assert( Vec_PtrSize(p->vCellClasses) == 0 );
    SC_LibForEachCell( p, pCell, i )
    {
        // find gate with the same function
        SC_LibForEachCellClass( p, pRepr, k )
            if ( pCell->n_inputs  == pRepr->n_inputs && 
                 pCell->n_outputs == pRepr->n_outputs && 
                 Vec_WrdEqual(SC_CellFunc(pCell), SC_CellFunc(pRepr)) )
                break;
        if ( k == Vec_PtrSize(p->vCellClasses) )
        {
            Vec_PtrPush( p->vCellClasses, pCell );
            pCell->pNext = pCell->pPrev = pCell;
            continue;
        }
        // add it to the list before the cell
        pRepr->pPrev->pNext = pCell; pCell->pNext = pRepr;
        pCell->pPrev = pRepr->pPrev; pRepr->pPrev = pCell;
    }
    // sort cells by size the then by name
    qsort( (void *)Vec_PtrArray(p->vCellClasses), Vec_PtrSize(p->vCellClasses), sizeof(void *), (int(*)(const void *,const void *))Abc_SclCompareCells );
    // sort cell lists
    SC_LibForEachCellClass( p, pRepr, k )
    {
        Vec_Ptr_t * vList = Vec_PtrAlloc( 100 );
        SC_RingForEachCell( pRepr, pCell, i )
            Vec_PtrPush( vList, pCell );
        qsort( (void *)Vec_PtrArray(vList), Vec_PtrSize(vList), sizeof(void *), (int(*)(const void *,const void *))Abc_SclCompareCells );
        // create new representative
        pRepr = (SC_Cell *)Vec_PtrEntry( vList, 0 );
        pRepr->pNext = pRepr->pPrev = pRepr;
        pRepr->Order = 0;
        // relink cells
        Vec_PtrForEachEntryStart( SC_Cell *, vList, pCell, i, 1 )
        {
            pRepr->pPrev->pNext = pCell; pCell->pNext = pRepr;
            pCell->pPrev = pRepr->pPrev; pRepr->pPrev = pCell;
            pCell->Order = i;
        }
        // update list
        Vec_PtrWriteEntry( p->vCellClasses, k, pRepr );
        Vec_PtrFree( vList );
    }
}
void Abc_SclPrintCells( SC_Lib * p )
{
    SC_Cell * pCell, * pRepr;
    int i, k, j, nLength = 0;
    assert( Vec_PtrSize(p->vCellClasses) > 0 );
    printf( "Library \"%s\" ", p->pName );
    printf( "containing %d cells in %d classes.\n", 
        Vec_PtrSize(p->vCells), Vec_PtrSize(p->vCellClasses) );
    // find the longest name
    SC_LibForEachCellClass( p, pRepr, k )
        SC_RingForEachCell( pRepr, pCell, i )
            nLength = Abc_MaxInt( nLength, strlen(pRepr->pName) );
    // print cells
    SC_LibForEachCellClass( p, pRepr, k )
    {
        printf( "Class%3d : ", k );
        printf( "Ins = %d  ",  pRepr->n_inputs );
        printf( "Outs = %d",   pRepr->n_outputs );
        for ( i = 0; i < pRepr->n_outputs; i++ )
        {
            printf( "   "  );
            Kit_DsdPrintFromTruth( (unsigned *)Vec_WrdArray(SC_CellPin(pRepr, pRepr->n_inputs+i)->vFunc), pRepr->n_inputs );
        }
        printf( "\n" );
        SC_RingForEachCell( pRepr, pCell, i )
        {
            printf( "  %3d : ",       i+1 );
            printf( "%-*s  ",         nLength, pCell->pName );
            printf( "%2d   ",         pCell->drive_strength );
            printf( "A =%8.2f  D =", pCell->area );
            // print linear approximation
            for ( j = 0; j < 3; j++ )
            {
                SC_Pin * pPin = SC_CellPin( pCell, pCell->n_inputs );
                if ( Vec_PtrSize(pPin->vRTimings) > 0 )
                {
                    SC_Timings * pRTime = (SC_Timings *)Vec_PtrEntry( pPin->vRTimings, 0 );
                    SC_Timing * pTime = (SC_Timing *)Vec_PtrEntry( pRTime->vTimings, 0 );
                    printf( " %6.2f", j ? pTime->pCellRise->approx[0][j] : SC_LibTimePs(p, pTime->pCellRise->approx[0][j]) );
                }
            }
            // print input capacitance
            printf( "   Cap =" );
            for ( j = 0; j < pCell->n_inputs; j++ )
            {
                SC_Pin * pPin = SC_CellPin( pCell, j );
                printf( " %6.2f", SC_LibCapFf(p, pPin->rise_cap) );
            }
            printf( "\n" );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Converts pNode->pData gates into array of SC_Lit gate IDs and back.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_SclManFindGates( SC_Lib * pLib, Abc_Ntk_t * p )
{
    Vec_Int_t * vVec;
    Abc_Obj_t * pObj;
    int i;
    vVec = Vec_IntStartFull( Abc_NtkObjNumMax(p) );
    Abc_NtkForEachNode1( p, pObj, i )
    {
        char * pName = Mio_GateReadName((Mio_Gate_t *)pObj->pData);
        int gateId = Abc_SclCellFind( pLib, pName );
        assert( gateId >= 0 );
        Vec_IntWriteEntry( vVec, i, gateId );
//printf( "Found gate %s\n", pName );
    }
    return vVec;
}
void Abc_SclManSetGates( SC_Lib * pLib, Abc_Ntk_t * p, Vec_Int_t * vGates )
{
    Abc_Obj_t * pObj;
    int i;
    Abc_NtkForEachNode1( p, pObj, i )
    {
        SC_Cell * pCell = SC_LibCell( pLib, Vec_IntEntry(vGates, Abc_ObjId(pObj)) );
        assert( pCell->n_inputs == Abc_ObjFaninNum(pObj) );
        pObj->pData = Mio_LibraryReadGateByName( (Mio_Library_t *)p->pManFunc, pCell->pName, NULL );
        assert( pObj->fMarkA == 0 && pObj->fMarkB == 0 );
//printf( "Found gate %s\n", pCell->name );
    }
}

/**Function*************************************************************

  Synopsis    [Reports percentage of gates of each size.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
#define ABC_SCL_MAX_SIZE 64
void Abc_SclManPrintGateSizes( SC_Lib * pLib, Abc_Ntk_t * p, Vec_Int_t * vGates )
{
    Abc_Obj_t * pObj;
    int i, nGates = 0, Counters[ABC_SCL_MAX_SIZE] = {0};
    double TotArea = 0, Areas[ABC_SCL_MAX_SIZE] = {0};
    Abc_NtkForEachNode1( p, pObj, i )
    {
        SC_Cell * pCell = SC_LibCell( pLib, Vec_IntEntry(vGates, Abc_ObjId(pObj)) );
        assert( pCell->Order < ABC_SCL_MAX_SIZE );
        Counters[pCell->Order]++;
        Areas[pCell->Order] += pCell->area;
        TotArea += pCell->area;
        nGates++;
    }
    printf( "Total gates = %d.  Total area = %.1f\n", nGates, TotArea );
    for ( i = 0; i < ABC_SCL_MAX_SIZE; i++ )
    {
        if ( Counters[i] == 0 )
            continue;
        printf( "Cell size = %d.  ", i );
        printf( "Count = %6d  ",     Counters[i] );
        printf( "(%5.1f %%)   ",     100.0 * Counters[i] / nGates );
        printf( "Area = %12.1f  ",   Areas[i] );
        printf( "(%5.1f %%)  ",      100.0 * Areas[i] / TotArea );
        printf( "\n" );
    }
}
void Abc_SclPrintGateSizes( SC_Lib * pLib, Abc_Ntk_t * p )
{
    Vec_Int_t * vGates;
    vGates = Abc_SclManFindGates( pLib, p );
    Abc_SclManPrintGateSizes( pLib, p, vGates );
    Vec_IntFree( vGates );
}

/**Function*************************************************************

  Synopsis    [Downsizes each gate to its minimium size.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
SC_Cell * Abc_SclFindMaxAreaCell( SC_Cell * pRepr )
{
    SC_Cell * pCell, * pBest = pRepr;
    float AreaBest = pRepr->area;
    int i;
    SC_RingForEachCell( pRepr, pCell, i )
        if ( AreaBest < pCell->area )
        {
            AreaBest = pCell->area;
            pBest = pCell;
        }
    return pBest;
}
void Abc_SclMinsizePerform( SC_Lib * pLib, Abc_Ntk_t * p, int fUseMax, int fVerbose )
{
    Vec_Int_t * vMinCells, * vGates;
    SC_Cell * pCell, * pRepr = NULL, * pBest = NULL;
    Abc_Obj_t * pObj;
    int i, k, gateId;
    // map each gate in the library into its min-size prototype
    vMinCells = Vec_IntStartFull( Vec_PtrSize(pLib->vCells) );
    SC_LibForEachCellClass( pLib, pRepr, i )
    {
        pBest = fUseMax ? Abc_SclFindMaxAreaCell(pRepr) : pRepr;
        SC_RingForEachCell( pRepr, pCell, k )
            Vec_IntWriteEntry( vMinCells, pCell->Id, pBest->Id );
    }
    // update each cell
    vGates = Abc_SclManFindGates( pLib, p );
    Abc_NtkForEachNode1( p, pObj, i )
    {
        gateId = Vec_IntEntry( vGates, i );
        assert( gateId >= 0 && gateId < Vec_PtrSize(pLib->vCells) );
        gateId = Vec_IntEntry( vMinCells, gateId );
        assert( gateId >= 0 && gateId < Vec_PtrSize(pLib->vCells) );
        Vec_IntWriteEntry( vGates, i, gateId );
    }
    Abc_SclManSetGates( pLib, p, vGates );
    Vec_IntFree( vMinCells );
    Vec_IntFree( vGates );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

