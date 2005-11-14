/**CFile****************************************************************

  FileName    [pgaMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapper.]

  Synopsis    [Mapping manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: pgaMan.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "pgaInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Cut_Man_t * Pga_ManStartCutMan( Pga_Params_t * pParamsPga );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Pga_Man_t * Pga_ManStart( Pga_Params_t * pParams )
{
    Pga_Man_t * p;
    Pga_Node_t * pNode;
    Cut_Man_t * pManCut;
    Abc_Ntk_t * pNtk;
    Abc_Obj_t * pObj;
    int i, Counter;
    int clk = clock();

    // make sure the network is given
    pNtk = pParams->pNtk;
    if ( pNtk == NULL )
    {
        printf( "Network is not specified.\n" );
        return NULL;
    }
    if ( !Abc_NtkIsStrash(pNtk) )
    {
        printf( "Mapping can only be applied to an AIG.\n" );
        return NULL;
    }
    // the cut manager if given should be in sinc
    pManCut = pNtk->pManCut;
    if ( pManCut && Cut_ManReadVarsMax(pManCut) != Fpga_LutLibReadVarMax(pParams->pLutLib) )
    {
        printf( "The precomputed cuts have different size.\n" );
        return NULL;
    }
    // make sure the nodes are in the topological order
    if ( !Abc_NtkIsDfsOrdered(pNtk) )
    {
        printf( "The nodes of the network are not DFS ordered.\n" );
//        Abc_NtkReassignIds( pNtk );
        return NULL;
    }
    // make sure there are no dangling nodes (unless they are choices)

    // start the mapping manager
    p = ALLOC( Pga_Man_t, 1 );
    memset( p, 0, sizeof(Pga_Man_t) );
    p->pParams    = pParams;
    p->nVarsMax   = Fpga_LutLibReadVarMax(pParams->pLutLib);
    p->pManCut    = pManCut? pManCut : Pga_ManStartCutMan(pParams);
    p->vOrdering  = Abc_AigGetLevelizedOrder(pNtk, 0);  // what happens with dangling nodes???
    p->pLutAreas  = Fpga_LutLibReadLutAreas(pParams->pLutLib);
    p->pLutDelays = Fpga_LutLibReadLutDelays(pParams->pLutLib);
    p->Epsilon    = (float)0.00001;

    // allocate mapping structures
    p->pMemory  = ALLOC( Pga_Node_t, Abc_NtkObjNum(pNtk) );
    memset( p->pMemory, 0, sizeof(Pga_Node_t) * Abc_NtkObjNum(pNtk) );
    p->vStructs = Vec_PtrStart( Abc_NtkObjNumMax(pNtk) );
    Counter = 0;
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        pNode = p->pMemory + Counter++;
        pNode->Id          = pObj->Id;
        pNode->nRefs       = pObj->vFanouts.nSize;
        pNode->Required    = ABC_INFINITY;
        pNode->Match.Area  = ABC_INFINITY;
        // skip secondary nodes
        if ( Abc_ObjFanoutNum(pObj) == 0 )
            continue;
        Vec_PtrWriteEntry( p->vStructs, pObj->Id, pNode );
    }
    assert( Counter == Abc_NtkObjNum(pNtk) );
    // update order to depend on mapping nodes
    Vec_PtrForEachEntry( p->vOrdering, pObj, i )
        Vec_PtrWriteEntry( p->vOrdering, i, Pga_Node(p,pObj->Id) );
p->timeToMap = clock() - clk;
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pga_ManStop( Pga_Man_t * p )
{
    Cut_ManStop( p->pManCut );
    Vec_PtrFree( p->vOrdering );
    Vec_PtrFree( p->vStructs );
    free( p->pMemory );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Starts the cut manager for FPGA mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Cut_Man_t * Pga_ManStartCutMan( Pga_Params_t * pParamsPga )
{
    static Cut_Params_t Params, * pParams = &Params;
    Abc_Ntk_t * pNtk = pParamsPga->pNtk;
    Cut_Man_t * pManCut;
    Abc_Obj_t * pObj;
    int i;
    // start the cut manager
    memset( pParams, 0, sizeof(Cut_Params_t) );
    pParams->nVarsMax  = Fpga_LutLibReadVarMax(pParamsPga->pLutLib); // max cut size
    pParams->nKeepMax  = 250;   // the max number of cuts kept at a node
    pParams->fTruth    = 0;     // compute truth tables
    pParams->fFilter   = 1;     // filter dominated cuts
    pParams->fSeq      = 0;     // compute sequential cuts
    pParams->fDrop     = pParamsPga->fDropCuts; // drop cuts on the fly
    pParams->fVerbose  = 0;     // the verbosiness flag
    pParams->nIdsMax   = Abc_NtkObjNumMax( pNtk );
    pManCut = Cut_ManStart( pParams );
    if ( pParams->fDrop )
        Cut_ManSetFanoutCounts( pManCut, Abc_NtkFanoutCounts(pNtk) );
    // set cuts for PIs
    Abc_NtkForEachCi( pNtk, pObj, i )
        if ( Abc_ObjFanoutNum(pObj) > 0 )
            Cut_NodeSetTriv( pManCut, pObj->Id );
    return pManCut;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


