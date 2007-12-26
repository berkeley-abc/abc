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
    pDelayTable = ALLOC( float, nIns * nOuts );
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
    int i, curPi, curPo, Entry;
    assert( p->pAig != NULL );
    // start the timing manager
    pMan = Tim_ManStart( Aig_ManPiNum(p->pAig), Aig_ManPoNum(p->pAig) );
    // add arrival time info for the true PIs
    pRoot = Vec_PtrEntry( p->vModels, 0 );
    Ntl_ModelForEachPi( pRoot, pObj, i )
        Tim_ManInitPiArrival( pMan, i, 0.0 );
    // unpack the data in the arrival times
    if ( pRoot->vArrivals )
        Vec_IntForEachEntry( pRoot->vArrivals, Entry, i )
            Tim_ManInitPiArrival( pMan, Entry, Vec_IntEntry(pRoot->vArrivals,++i) );
    // add the required time into for the true POs
    pRoot = Vec_PtrEntry( p->vModels, 0 );
    Ntl_ModelForEachPo( pRoot, pObj, i )
        Tim_ManInitPoRequired( pMan, i, AIG_INFINITY );
    // unpack the data in the required times
    if ( pRoot->vRequireds )
        Vec_IntForEachEntry( pRoot->vRequireds, Entry, i )
            Tim_ManInitPoRequired( pMan, Entry, Vec_IntEntry(pRoot->vRequireds,++i) );
    // derive timing tables
    vDelayTables = Vec_PtrAlloc( Vec_PtrSize(p->vModels) );
    Ntl_ManForEachModel( p, pModel, i )
    {
        if ( pModel->vDelays )
            pModel->pDelayTable = Ntl_ManCreateDelayTable( pModel->vDelays, Ntl_ModelPiNum(pModel), Ntl_ModelPoNum(pModel) );
        Vec_PtrPush( vDelayTables, pModel->pDelayTable );
    }
    Tim_ManSetDelayTables( pMan, vDelayTables );
    // set up the boxes
    curPi = Ntl_ModelPiNum(pRoot);
    curPo = Ntl_ModelPoNum(pRoot);
    Ntl_ManForEachBox( p, pObj, i )
    {
        Tim_ManCreateBoxFirst( pMan, curPo, Ntl_ObjFanoutNum(pObj), curPi, Ntl_ObjFaninNum(pObj), pObj->pImplem->pDelayTable );
        curPo += Ntl_ObjFanoutNum(pObj);
        curPi += Ntl_ObjFaninNum(pObj);
    }
    // forget refs to the delay tables in the network
    Ntl_ManForEachModel( p, pModel, i )
        pModel->pDelayTable = NULL;
    return pMan;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


