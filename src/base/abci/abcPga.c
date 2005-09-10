/**CFile****************************************************************

  FileName    [abcPga.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Interface with the FPGA mapping package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcPga.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "fraig.h"
#include "fpga.h"
#include "pga.h"
#include "cut.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Abc_Ntk_t * Abc_NtkFromPga( Abc_Ntk_t * pNtk, Vec_Ptr_t * vNodeCuts );
 
////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Interface with the FPGA mapping package.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkPga( Pga_Params_t * pParams )
{
    Abc_Ntk_t * pNtkNew, * pNtk = pParams->pNtk;
    Pga_Man_t * pMan;
    Vec_Ptr_t * vNodeCuts;

    assert( Abc_NtkIsStrash(pNtk) );

    // print a warning about choice nodes
    if ( Abc_NtkGetChoiceNum( pNtk ) )
        printf( "Performing FPGA mapping with choices.\n" );

    // start the mapping manager
    pMan = Pga_ManStart( pParams );    
    if ( pMan == NULL )
        return NULL;

    // perform mapping
    vNodeCuts = Pga_DoMapping( pMan );

    // transform the result of mapping into a BDD logic network
    pNtkNew = Abc_NtkFromPga( pNtk, vNodeCuts );
    if ( pNtkNew == NULL )
        return NULL;
    Pga_ManStop( pMan );
    Vec_PtrFree( vNodeCuts );

    // make the network minimum base
    Abc_NtkMinimumBase( pNtkNew );

    // make sure that everything is okay
    if ( !Abc_NtkCheck( pNtkNew ) )
    {
        printf( "Abc_NtkPga: The network check has failed.\n" );
        Abc_NtkDelete( pNtkNew );
        return NULL;
    }
    return pNtkNew;
}


/**Function*************************************************************

  Synopsis    [Creates the mapped network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkFromPga( Abc_Ntk_t * pNtk, Vec_Ptr_t * vNodeCuts )
{
    ProgressBar * pProgress;
    DdManager * dd;
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pNode, * pFanin, * pNodeNew;
    Cut_Cut_t * pCut;
    Vec_Ptr_t * vLeaves, * vVisited;
    int i, k, nDupGates;
    // create the new network
    pNtkNew = Abc_NtkStartFrom( pNtk, ABC_TYPE_LOGIC, ABC_FUNC_BDD );
    dd = pNtkNew->pManFunc;
    // set the constant node
    pNode = Abc_AigConst1(pNtk->pManFunc);
    if ( Abc_ObjFanoutNum(pNode) > 0 )
        pNode->pCopy = Abc_NodeCreateConst1(pNtkNew);
    // add new nodes in topologic order
    vLeaves  = Vec_PtrAlloc( 6 );
    vVisited = Vec_PtrAlloc( 100 );
    pProgress = Extra_ProgressBarStart( stdout, Vec_PtrSize(vNodeCuts) );
    Vec_PtrForEachEntry( vNodeCuts, pCut, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        // create the new node
        pNodeNew = Abc_NtkCreateNode( pNtkNew );
        Vec_PtrClear( vLeaves );
        for ( k = 0; k < (int)pCut->nLeaves; k++ )
        {
            // add the node representing the old fanin in the new network
            pFanin = Abc_NtkObj( pNtk, pCut->pLeaves[k] );
            Vec_PtrPush( vLeaves, pFanin );
            Abc_ObjAddFanin( pNodeNew, pFanin->pCopy );
        }
        // set the new node at the old node
        pNode = Abc_NtkObj( pNtk, pCut->uSign );  // pCut->uSign contains the ID of the root node
        pNode->pCopy = pNodeNew;
        // create the function of the new node
        pNodeNew->pData = Abc_NodeConeBdd( dd, dd->vars, pNode, vLeaves, vVisited );   Cudd_Ref( pNodeNew->pData );
    }
    Extra_ProgressBarStop( pProgress );
    Vec_PtrFree( vVisited );
    Vec_PtrFree( vLeaves );
    // finalize the new network
    Abc_NtkFinalize( pNtk, pNtkNew );
    // decouple the PO driver nodes to reduce the number of levels
    nDupGates = Abc_NtkLogicMakeSimpleCos( pNtkNew, 1 );
//    if ( nDupGates && Fpga_ManReadVerbose(pMan) )
//        printf( "Duplicated %d gates to decouple the CO drivers.\n", nDupGates );
    return pNtkNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


