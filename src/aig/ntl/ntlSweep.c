/**CFile****************************************************************

  FileName    [ntlSweep.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Performs structural sweep of the netlist.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntlSweep.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntl.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Detects logic that does not fanout into POs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManSweepMark_rec( Ntl_Man_t * p, Ntl_Obj_t * pObj )
{
    Ntl_Net_t * pNet;
    int i;
    if ( pObj->fMark )
        return;
    pObj->fMark = 1;
    Ntl_ObjForEachFanin( pObj, pNet, i )
        Ntl_ManSweepMark_rec( p, pNet->pDriver );
}

/**Function*************************************************************

  Synopsis    [Detects logic that does not fanout into POs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManSweepMark( Ntl_Man_t * p )
{
    Ntl_Mod_t * pRoot;
    Ntl_Obj_t * pObj;
    int i;
    // get the root model
    pRoot = Ntl_ManRootModel( p );
    // clear net visited flags
    Ntl_ModelForEachObj( pRoot, pObj, i )
        assert( pObj->fMark == 0 );
    // label the primary inputs
    Ntl_ModelForEachPi( pRoot, pObj, i )
        pObj->fMark = 1;
    // start from the primary outputs
    Ntl_ModelForEachPo( pRoot, pObj, i )
        Ntl_ManSweepMark_rec( p, pObj );
}

/**Function*************************************************************

  Synopsis    [Derives new netlist by sweeping current netlist with the current AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Man_t * Ntl_ManSweep( Ntl_Man_t * p, Aig_Man_t * pAig, int fVerbose )
{
    int nObjsOld[NTL_OBJ_VOID];
    Ntl_Man_t * pNew;
    Ntl_Mod_t * pRoot;
    Ntl_Net_t * pNet;
    Ntl_Obj_t * pObj;
    int i, k, nNetsOld;

    // insert the AIG into the netlist
    pNew = Ntl_ManInsertAig( p, pAig );
    if ( pNew == NULL )
    {
        printf( "Ntl_ManSweep(): Inserting AIG has failed.\n" );
        return NULL;
    }

    // remember the number of objects
    pRoot = Ntl_ManRootModel( pNew );
    for ( i = 0; i < NTL_OBJ_VOID; i++ )
        nObjsOld[i] = pRoot->nObjs[i];
    nNetsOld = Ntl_ModelCountNets(pRoot);

    // mark the nets that do not fanout into POs
    Ntl_ManSweepMark( pNew );

    // remove the useless objects and their nets
    Ntl_ModelForEachObj( pRoot, pObj, i )
    {
        if ( pObj->fMark )
        {
            pObj->fMark = 0;
            continue;
        }
        // remove the fanout nets
        Ntl_ObjForEachFanout( pObj, pNet, k )
            Ntl_ModelDeleteNet( pRoot, Ntl_ObjFanout0(pObj) );
        // remove the object
        if ( Ntl_ObjIsNode(pObj) && Ntl_ObjFaninNum(pObj) == 1 )
            pRoot->nObjs[NTL_OBJ_LUT1]--;
        else
            pRoot->nObjs[pObj->Type]--;
        Vec_PtrWriteEntry( pRoot->vObjs, pObj->Id, NULL );
        pObj->Id = NTL_OBJ_NONE;
    }

    // print detailed statistics of sweeping
    if ( fVerbose )
    {
        printf( "Sweep:" );
        printf( "  Node = %d (%4.1f %%)", 
            nObjsOld[NTL_OBJ_NODE] - pRoot->nObjs[NTL_OBJ_NODE],
            !nObjsOld[NTL_OBJ_NODE]? 0.0: 100.0 * (nObjsOld[NTL_OBJ_NODE] - pRoot->nObjs[NTL_OBJ_NODE]) / nObjsOld[NTL_OBJ_NODE] );
        printf( "  Buf/Inv = %d (%4.1f %%)", 
            nObjsOld[NTL_OBJ_LUT1] - pRoot->nObjs[NTL_OBJ_LUT1],
            !nObjsOld[NTL_OBJ_LUT1]? 0.0: 100.0 * (nObjsOld[NTL_OBJ_LUT1] - pRoot->nObjs[NTL_OBJ_LUT1]) / nObjsOld[NTL_OBJ_LUT1] );
        printf( "  Lat = %d (%4.1f %%)", 
            nObjsOld[NTL_OBJ_LATCH] - pRoot->nObjs[NTL_OBJ_LATCH],
            !nObjsOld[NTL_OBJ_LATCH]? 0.0: 100.0 * (nObjsOld[NTL_OBJ_LATCH] - pRoot->nObjs[NTL_OBJ_LATCH]) / nObjsOld[NTL_OBJ_LATCH] );
        printf( "  Box = %d (%4.1f %%)", 
            nObjsOld[NTL_OBJ_BOX] - pRoot->nObjs[NTL_OBJ_BOX],
            !nObjsOld[NTL_OBJ_BOX]? 0.0: 100.0 * (nObjsOld[NTL_OBJ_BOX] - pRoot->nObjs[NTL_OBJ_BOX]) / nObjsOld[NTL_OBJ_BOX] );
        printf( "\n" );
//        printf( "Also, sweep reduced %d nets.\n", nNetsOld - Ntl_ModelCountNets(pRoot) );
    }
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


