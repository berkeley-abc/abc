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

#include "sclSize.h"
#include "map/mio/mio.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

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
//        if ( SC_LibCell(pLib, gateId)->n_outputs > 1 )
//            continue;
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

