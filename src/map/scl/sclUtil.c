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
#include "base/main/main.h"

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
void Abc_SclMioGates2SclGates( SC_Lib * pLib, Abc_Ntk_t * p )
{
    Abc_Obj_t * pObj;
    int i;
    assert( p->vGates == NULL );
    p->vGates = Vec_IntStartFull( Abc_NtkObjNumMax(p) );
    Abc_NtkForEachNode1( p, pObj, i )
    {
        char * pName = Mio_GateReadName((Mio_Gate_t *)pObj->pData);
        int gateId = Abc_SclCellFind( pLib, pName );
        assert( gateId >= 0 );
        Vec_IntWriteEntry( p->vGates, i, gateId );
//printf( "Found gate %s\n", pName );
    }
    p->pSCLib = pLib;
}
void Abc_SclSclGates2MioGates( SC_Lib * pLib, Abc_Ntk_t * p )
{
    Abc_Obj_t * pObj;
    int i, Counter = 0, CounterAll = 0;
    assert( p->vGates != NULL );
    Abc_NtkForEachNode1( p, pObj, i )
    {
        SC_Cell * pCell = Abc_SclObjCell(pObj);
        assert( pCell->n_inputs == Abc_ObjFaninNum(pObj) );
        pObj->pData = Mio_LibraryReadGateByName( (Mio_Library_t *)p->pManFunc, pCell->pName, NULL );
        Counter += (pObj->pData == NULL);
        assert( pObj->fMarkA == 0 && pObj->fMarkB == 0 );
        CounterAll++;
//printf( "Found gate %s\n", pCell->name );
    }
    if ( Counter )
        printf( "Could not find %d (out of %d) gates in the current library.\n", Counter, CounterAll );
    Vec_IntFreeP( &p->vGates );
    p->pSCLib = NULL;
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
    Abc_SclMioGates2SclGates( pLib, p );
    Abc_SclManPrintGateSizes( pLib, p, p->vGates );
    Vec_IntFreeP( &p->vGates );
    p->pSCLib = NULL;
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
Vec_Int_t * Abc_SclFindMinAreas( SC_Lib * pLib, int fUseMax )
{
    Vec_Int_t * vMinCells;
    SC_Cell * pCell, * pRepr = NULL, * pBest = NULL;
    int i, k;
    // map each gate in the library into its min/max-size prototype
    vMinCells = Vec_IntStartFull( Vec_PtrSize(pLib->vCells) );
    SC_LibForEachCellClass( pLib, pRepr, i )
    {
        pBest = fUseMax ? Abc_SclFindMaxAreaCell(pRepr) : pRepr;
        SC_RingForEachCell( pRepr, pCell, k )
            Vec_IntWriteEntry( vMinCells, pCell->Id, pBest->Id );
    }
    return vMinCells;
}
void Abc_SclMinsizePerform( SC_Lib * pLib, Abc_Ntk_t * p, int fUseMax, int fVerbose )
{
    Vec_Int_t * vMinCells;
    Abc_Obj_t * pObj;
    int i, gateId;
    vMinCells = Abc_SclFindMinAreas( pLib, fUseMax );
    Abc_SclMioGates2SclGates( pLib, p );
    Abc_NtkForEachNode1( p, pObj, i )
    {
        gateId = Vec_IntEntry( p->vGates, i );
        assert( gateId >= 0 && gateId < Vec_PtrSize(pLib->vCells) );
        gateId = Vec_IntEntry( vMinCells, gateId );
        assert( gateId >= 0 && gateId < Vec_PtrSize(pLib->vCells) );
        Vec_IntWriteEntry( p->vGates, i, gateId );
    }
    Abc_SclSclGates2MioGates( pLib, p );
    Vec_IntFree( vMinCells );
}
int Abc_SclCountMinSize( SC_Lib * pLib, Abc_Ntk_t * p, int fUseMax )
{
    Vec_Int_t * vMinCells;
    Abc_Obj_t * pObj;
    int i, gateId, Counter = 0;
    vMinCells = Abc_SclFindMinAreas( pLib, fUseMax );
    Abc_NtkForEachNode1( p, pObj, i )
    {
        gateId = Vec_IntEntry( p->vGates, i );
        Counter += ( gateId == Vec_IntEntry(vMinCells, gateId) );
    }
    Vec_IntFree( vMinCells );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Returns gate formula by name.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_SclFindGateFormula( char * pGateName, char * pOutName )
{
    Mio_Library_t * pLib = (Mio_Library_t *)Abc_FrameReadLibGen();
    Mio_Gate_t * pGate = Mio_LibraryReadGateByName( pLib, pGateName, pOutName );
    return Mio_GateReadForm(pGate);
}

/**Function*************************************************************

  Synopsis    [Reads timing constraints.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclReadTimingConstr( Abc_Frame_t * pAbc, char * pFileName, int fVerbose )
{
    char Buffer[1000], * pToken;
    FILE * pFile = fopen( pFileName, "rb" );
    while ( fgets( Buffer, 1000, pFile ) )
    {
        pToken = strtok( Buffer, " \t\r\n" );
        if ( !strcmp(pToken, "set_driving_cell") )
        {
            Abc_FrameSetDrivingCell( Abc_UtilStrsav(strtok(NULL, " \t\r\n")) );
            if ( fVerbose ) 
                printf( "Setting driving cell to be \"%s\".\n", Abc_FrameReadDrivingCell() );
        }
        else if ( !strcmp(pToken, "set_load") )
        {
            Abc_FrameSetMaxLoad( atof(strtok(NULL, " \t\r\n")) );
            if ( fVerbose ) 
                printf( "Setting driving cell to be %f.\n", Abc_FrameReadMaxLoad() );
        }
        else 
            printf( "Unrecognized token \"%s\".\n", pToken );
    }
    fclose( pFile );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

