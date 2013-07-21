/**CFile****************************************************************

  FileName    [sclLoad.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Standard-cell library representation.]

  Synopsis    [Wire/gate load computations.]

  Author      [Alan Mishchenko, Niklas Een]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - August 24, 2012.]

  Revision    [$Id: sclLoad.c,v 1.0 2012/08/24 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sclInt.h"
#include "sclMan.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the wireload model for the given area.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
SC_WireLoad * Abc_SclFindWireLoadModel( SC_Lib * p, float Area )
{
    SC_WireLoad * pWL = NULL;
    char * pWLoadUsed = NULL;
    int i;
    if ( p->default_wire_load_sel && strlen(p->default_wire_load_sel) )
    {
        SC_WireLoadSel * pWLS = NULL;
        SC_LibForEachWireLoadSel( p, pWLS, i )
            if ( !strcmp(pWLS->pName, p->default_wire_load_sel) )
                break;
        if ( i == Vec_PtrSize(p->vWireLoadSels) )
        {
            Abc_Print( -1, "Cannot find wire load selection model \"%s\".\n", p->default_wire_load_sel );
            exit(1);
        }
        for ( i = 0; i < Vec_FltSize(pWLS->vAreaFrom); i++)
            if ( Area >= Vec_FltEntry(pWLS->vAreaFrom, i) && Area <  Vec_FltEntry(pWLS->vAreaTo, i) )
            {
                pWLoadUsed = (char *)Vec_PtrEntry(pWLS->vWireLoadModel, i);
                break;
            }
        if ( i == Vec_FltSize(pWLS->vAreaFrom) )
            pWLoadUsed = (char *)Vec_PtrEntryLast(pWLS->vWireLoadModel);
    }
    else if ( p->default_wire_load && strlen(p->default_wire_load) )
        pWLoadUsed = p->default_wire_load;
    else
    {
        Abc_Print( 0, "No wire model given.\n" );
        return NULL;
    }
    // Get the actual table and reformat it for 'wire_cap' output:
    assert( pWLoadUsed != NULL );
    SC_LibForEachWireLoad( p, pWL, i )
        if ( !strcmp(pWL->pName, pWLoadUsed) )
            break;
    if ( i == Vec_PtrSize(p->vWireLoads) )
    {
        Abc_Print( -1, "Cannot find wire load model \"%s\".\n", pWLoadUsed );
        exit(1);
    }
//    printf( "Using wireload model \"%s\".\n", pWL->pName );
    return pWL;
}

/**Function*************************************************************

  Synopsis    [Returns estimated wire capacitances for each fanout count.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Flt_t * Abc_SclFindWireCaps( SC_Man * p, SC_WireLoad * pWL )
{
    Vec_Flt_t * vCaps = NULL;
    float EntryPrev, EntryCur;
    int i, Entry, EntryMax;
    assert( pWL != NULL );
    // find the biggest fanout
    EntryMax = 0;
    Vec_IntForEachEntry( pWL->vFanout, Entry, i )
        EntryMax = Abc_MaxInt( EntryMax, Entry );
    // create the array
    vCaps = Vec_FltStart( EntryMax + 1 );
    Vec_IntForEachEntry( pWL->vFanout, Entry, i )
        Vec_FltWriteEntry( vCaps, Entry, Vec_FltEntry(pWL->vLen, i) * pWL->cap );
    // reformat
    EntryPrev = 0;
    Vec_FltForEachEntry( vCaps, EntryCur, i )
    {
        if ( EntryCur )
            EntryPrev = EntryCur;
        else
            Vec_FltWriteEntry( vCaps, i, EntryPrev );
    }
    return vCaps;
}

/**Function*************************************************************

  Synopsis    [Computes load for all nodes in the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclComputeLoad( SC_Man * p )
{
    Vec_Flt_t * vWireCaps;
    Abc_Obj_t * pObj, * pFanin;
    int i, k;
    // clear load storage
    Abc_NtkForEachObj( p->pNtk, pObj, i )
    {
        SC_Pair * pLoad = Abc_SclObjLoad( p, pObj );
        if ( !Abc_ObjIsPo(pObj) )
            pLoad->rise = pLoad->fall = 0.0;
    }
    // add cell load
    Abc_NtkForEachNode1( p->pNtk, pObj, i )
    {
        SC_Cell * pCell = Abc_SclObjCell( p, pObj );
        Abc_ObjForEachFanin( pObj, pFanin, k )
        {
            SC_Pair * pLoad = Abc_SclObjLoad( p, pFanin );
            SC_Pin * pPin = SC_CellPin( pCell, k );
            pLoad->rise += pPin->rise_cap;
            pLoad->fall += pPin->fall_cap;
        }
    }
    // add PO load
    Abc_NtkForEachPo( p->pNtk, pObj, i )
    {
        SC_Pair * pLoadPo = Abc_SclObjLoad( p, pObj );
        SC_Pair * pLoad = Abc_SclObjLoad( p, Abc_ObjFanin0(pObj) );
        pLoad->rise += pLoadPo->rise;
        pLoad->fall += pLoadPo->fall;
    }
    if ( p->pWLoadUsed == NULL )
        return;
    // add wire load
    vWireCaps = Abc_SclFindWireCaps( p, p->pWLoadUsed );
    Abc_NtkForEachNode1( p->pNtk, pObj, i )
    {
        SC_Pair * pLoad = Abc_SclObjLoad( p, pObj );
        k = Abc_MinInt( Vec_FltSize(vWireCaps)-1, Abc_ObjFanoutNum(pObj) );
        pLoad->rise += Vec_FltEntry(vWireCaps, k);
        pLoad->fall += Vec_FltEntry(vWireCaps, k);
    }
    Vec_FltFree( vWireCaps );
}

/**Function*************************************************************

  Synopsis    [Updates load of the node's fanins.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_SclUpdateLoad( SC_Man * p, Abc_Obj_t * pObj, SC_Cell * pOld, SC_Cell * pNew )
{
    Abc_Obj_t * pFanin;
    int k;
    Abc_ObjForEachFanin( pObj, pFanin, k )
    {
        SC_Pair * pLoad = Abc_SclObjLoad( p, pFanin );
        SC_Pin * pPinOld = SC_CellPin( pOld, k );
        SC_Pin * pPinNew = SC_CellPin( pNew, k );
        pLoad->rise += pPinNew->rise_cap - pPinOld->rise_cap;
        pLoad->fall += pPinNew->fall_cap - pPinOld->fall_cap;
    }
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

