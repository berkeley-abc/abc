/**CFile****************************************************************

  FileName    [ntlTime.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Creates timing manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntlTime.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntl.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float * Ntl_ManCreateDelayTable( Vec_Int_t * vDelays, int nIns, int nOuts )
{
    float * pDelayTable, Delay;
    int iIn, iOut, i, k;
    assert( Vec_IntSize(vDelays) % 3 == 0 );
    pDelayTable = ABC_ALLOC( float, nIns * nOuts );
    memset( pDelayTable, 0, sizeof(float) * nIns * nOuts );
    Vec_IntForEachEntry( vDelays, iIn, i )
    {
        iOut = Vec_IntEntry(vDelays, ++i);
        Delay = Aig_Int2Float( Vec_IntEntry(vDelays, ++i) );
        if ( iIn == -1 && iOut == -1 )
            for ( k = 0; k < nIns * nOuts; k++ )
                pDelayTable[k] = Delay;
        else if ( iIn == -1 )
            for ( k = 0; k < nIns; k++ )
                pDelayTable[iOut * nIns + k] = Delay;
        else if ( iOut == -1 )
            for ( k = 0; k < nOuts; k++ )
                pDelayTable[k * nIns + iIn] = Delay;
        else 
            pDelayTable[iOut * nIns + iIn] = Delay;
    }
    return pDelayTable;
}

/**Function*************************************************************

  Synopsis    [Records the arrival times for the map leaves.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManUnpackLeafTiming( Ntl_Man_t * p, Tim_Man_t * pMan )
{
    Vec_Int_t * vTimes;
    Ntl_Mod_t * pRoot;
    Ntl_Obj_t * pObj;
    Ntl_Net_t * pNet;
    float dTime;
    int i, k, v, Entry, Counter;
    // clean the place
    pRoot = Ntl_ManRootModel( p );
    Ntl_ModelForEachMapLeaf( pRoot, pObj, i )
        Ntl_ObjForEachFanout( pObj, pNet, k )
            pNet->dTemp = 0;
    // store the PI timing
    vTimes = pRoot->vTimeInputs;
    if ( vTimes ) {
      Vec_IntForEachEntry( vTimes, Entry, i )
      {
          dTime = Aig_Int2Float( Vec_IntEntry(vTimes,++i) );
          if ( Entry == -1 )
          {
              Ntl_ModelForEachPi( pRoot, pObj, v )
                  Ntl_ObjFanout0(pObj)->dTemp = dTime;
          }
          else
          {
              pObj = Ntl_ModelPi( pRoot, Entry );
              Ntl_ObjFanout0(pObj)->dTemp = dTime;
          }
      }
    }
    // store box timing
    Ntl_ModelForEachMapLeaf( pRoot, pObj, k )
    {
        if ( !(Ntl_ObjIsBox(pObj) && Ntl_BoxIsSeq(pObj)) )
            continue;
        vTimes = pObj->pImplem->vTimeOutputs;
        if ( vTimes == NULL )
            continue;
        Vec_IntForEachEntry( vTimes, Entry, i )
        {
            dTime = Aig_Int2Float( Vec_IntEntry(vTimes,++i) );
            if ( Entry == -1 )
            {
                Ntl_ObjForEachFanout( pObj, pNet, v )
                    pNet->dTemp = dTime;
            }
            else
            {
                pNet = Ntl_ObjFanout( pObj, Entry );
                pNet->dTemp = dTime;
            }
        }
    }
    // load them into the timing manager
    Counter = 0;
    Ntl_ModelForEachMapLeaf( pRoot, pObj, i )
        Ntl_ObjForEachFanout( pObj, pNet, k )
        {
            if ( pNet->dTemp == TIM_ETERNITY )
                pNet->dTemp = -TIM_ETERNITY;
            Tim_ManInitCiArrival( pMan, Counter++, pNet->dTemp );
        }
    assert( Counter == p->iLastCi );
}

/**Function*************************************************************

  Synopsis    [Records the required times for the map leaves.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManUnpackRootTiming( Ntl_Man_t * p, Tim_Man_t * pMan )
{
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Tim_Man_t * Ntl_ManCreateTiming( Ntl_Man_t * p )
{
    Tim_Man_t * pMan;
    Vec_Ptr_t * vDelayTables;
    Ntl_Mod_t * pRoot, * pModel;
    Ntl_Obj_t * pObj;
    int i, curPi, iBox;//, Entry;
    assert( p->pAig != NULL );
    pRoot = Ntl_ManRootModel( p );
    // start the timing manager
    pMan = Tim_ManStart( Aig_ManPiNum(p->pAig), Aig_ManPoNum(p->pAig) );
    // unpack the timing data
    Ntl_ManUnpackLeafTiming( p, pMan );
//    Ntl_ManUnpackRootTiming( p, pMan );
/*
    if ( pRoot->vTimeInputs )
    {
        Vec_IntForEachEntry( pRoot->vTimeInputs, Entry, i )
        {
            if ( Entry == -1 )
                Tim_ManSetCiArrivalAll( pMan, Aig_Int2Float(Vec_IntEntry(pRoot->vTimeInputs,++i)) );
            else
                Tim_ManInitCiArrival( pMan, Entry, Aig_Int2Float(Vec_IntEntry(pRoot->vTimeInputs,++i)) );
        }
    }
    // unpack the data in the required times
    if ( pRoot->vTimeOutputs )
    {
        Vec_IntForEachEntry( pRoot->vTimeOutputs, Entry, i )
        {
            if ( Entry == -1 )
                Tim_ManSetCoRequiredAll( pMan, Aig_Int2Float(Vec_IntEntry(pRoot->vTimeOutputs,++i)) );
            else
                Tim_ManInitCoRequired( pMan, Entry, Aig_Int2Float(Vec_IntEntry(pRoot->vTimeOutputs,++i)) );
        }
    }
*/
    // derive timing tables for the whilte comb boxes
    vDelayTables = Vec_PtrAlloc( Vec_PtrSize(p->vModels) );
    Ntl_ManForEachModel( p, pModel, i )
    {
        if ( pModel->vDelays )
            pModel->pDelayTable = Ntl_ManCreateDelayTable( pModel->vDelays, Ntl_ModelPiNum(pModel), Ntl_ModelPoNum(pModel) );
        Vec_PtrPush( vDelayTables, pModel->pDelayTable );
    }
    Tim_ManSetDelayTables( pMan, vDelayTables );
    // set up the boxes
    iBox = 0;
    curPi = p->iLastCi;
    Vec_PtrForEachEntry( Ntl_Obj_t *, p->vVisNodes, pObj, i )
    {
        if ( !Ntl_ObjIsBox(pObj) )
            continue;
        Tim_ManCreateBoxFirst( pMan, Vec_IntEntry(p->vBox1Cios, iBox), Ntl_ObjFaninNum(pObj), curPi, Ntl_ObjFanoutNum(pObj), pObj->pImplem->pDelayTable );
        curPi += Ntl_ObjFanoutNum(pObj);
        iBox++;
    }
    // forget refs to the delay tables in the network
    Ntl_ManForEachModel( p, pModel, i )
        pModel->pDelayTable = NULL;
//    Tim_ManPrint( pMan );
    return pMan;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

