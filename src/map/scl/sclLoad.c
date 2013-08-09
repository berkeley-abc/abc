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

#include "sclSize.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns estimated wire capacitances for each fanout count.]

  Description []
               
  SideEffects []`

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
        SC_Cell * pCell = Abc_SclObjCell( pObj );
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
    // add wire load
    if ( p->pWLoadUsed != NULL )
    {
        vWireCaps = Abc_SclFindWireCaps( p, p->pWLoadUsed );
        Abc_NtkForEachNode1( p->pNtk, pObj, i )
        {
            SC_Pair * pLoad = Abc_SclObjLoad( p, pObj );
            k = Abc_MinInt( Vec_FltSize(vWireCaps)-1, Abc_ObjFanoutNum(pObj) );
            pLoad->rise += Vec_FltEntry(vWireCaps, k);
            pLoad->fall += Vec_FltEntry(vWireCaps, k);
        }
        Abc_NtkForEachPi( p->pNtk, pObj, i )
        {
            SC_Pair * pLoad = Abc_SclObjLoad( p, pObj );
            k = Abc_MinInt( Vec_FltSize(vWireCaps)-1, Abc_ObjFanoutNum(pObj) );
            pLoad->rise += Vec_FltEntry(vWireCaps, k);
            pLoad->fall += Vec_FltEntry(vWireCaps, k);
        }
        Vec_FltFree( vWireCaps );
    }
    // check input loads
    if ( p->pInDrive != NULL )
    {
        Abc_NtkForEachPi( p->pNtk, pObj, i )
        {
            SC_Pair * pLoad = Abc_SclObjLoad( p, pObj );
            if ( p->pInDrive[Abc_ObjId(pObj)] != 0 && (pLoad->rise > p->pInDrive[Abc_ObjId(pObj)] || pLoad->fall > p->pInDrive[Abc_ObjId(pObj)]) )
                printf( "Maximum input drive strength is exceeded at primary input %d.\n", i );
        }
    }
    // calculate average load
//    if ( p->EstLoadMax )
    {
        double TotalLoad = 0;
        int nObjs = 0;
        Abc_NtkForEachNode1( p->pNtk, pObj, i )
        {
            SC_Pair * pLoad = Abc_SclObjLoad( p, pObj );
            TotalLoad += 0.5 * pLoad->fall + 0.5 * pLoad->rise;
            nObjs++;
        }
        Abc_NtkForEachPi( p->pNtk, pObj, i )
        {
            SC_Pair * pLoad = Abc_SclObjLoad( p, pObj );
            TotalLoad += 0.5 * pLoad->fall + 0.5 * pLoad->rise;
            nObjs++;
        }
        p->EstLoadAve = (float)(TotalLoad / nObjs);
//        printf( "Average load = %.2f\n", p->EstLoadAve );
    }
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
void Abc_SclUpdateLoadSplit( SC_Man * p, Abc_Obj_t * pBuffer, Abc_Obj_t * pFanout )
{
    SC_Pin * pPin;
    SC_Pair * pLoad;
    int iFanin = Abc_NodeFindFanin( pFanout, pBuffer );
    assert( iFanin >= 0 );
    assert( Abc_ObjFaninNum(pBuffer) == 1 );
    pPin = SC_CellPin( Abc_SclObjCell(pFanout), iFanin );
    // update load of the buffer
    pLoad = Abc_SclObjLoad( p, pBuffer );
    pLoad->rise -= pPin->rise_cap;
    pLoad->fall -= pPin->fall_cap;
    // update load of the fanin
    pLoad = Abc_SclObjLoad( p, Abc_ObjFanin0(pBuffer) );
    pLoad->rise += pPin->rise_cap;
    pLoad->fall += pPin->fall_cap;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

