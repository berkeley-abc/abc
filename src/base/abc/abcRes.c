/**CFile****************************************************************

  FileName    [abcRes.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Technology-independent resynthesis of the AIG.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcRes.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "ft.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Abc_NodeUpdate( Abc_Obj_t * pNode, Vec_Ptr_t * vFanins, Vec_Int_t * vForm, int nGain );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs incremental rewriting of the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRewrite( Abc_Ntk_t * pNtk )
{
    int fCheck = 1;
    ProgressBar * pProgress;
    Abc_ManRwr_t * p;
    Abc_Obj_t * pNode;
    int i, nNodes, nGain;

    assert( Abc_NtkIsAig(pNtk) );
    // start the rewriting manager
    p = Abc_NtkManRwrStart( "data.aaa" );
    Abc_NtkManRwrStartCuts( p, pNtk );

    // resynthesize each node once
    nNodes = Abc_NtkObjNumMax(pNtk);
    pProgress = Extra_ProgressBarStart( stdout, nNodes );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, nNodes, NULL );
        // compute the cuts of the node
        Abc_NodeRwrComputeCuts( p, pNode );
        // for each cut, try to resynthesize it
        if ( (nGain = Abc_NodeRwrRewrite( p, pNode )) >= 0 )
            Abc_NodeUpdate( pNode, Abc_NtkManRwrFanins(p), Abc_NtkManRwrDecs(p), nGain );
        // check the improvement
        if ( i == nNodes )
            break;
    }
    Extra_ProgressBarStop( pProgress );

    // delete the manager
    Abc_NtkManRwrStop( p );
    // check
    if ( fCheck && !Abc_NtkCheck( pNtk ) )
    {
        printf( "Abc_NtkRewrite: The network check has failed.\n" );
        return 0;
    }
    return 1;
}


/**Function*************************************************************

  Synopsis    [Performs incremental resynthesis of the AIG.]

  Description [Starting from each node, computes a reconvergence-driven cut, 
  derives BDD of the cut function, constructs ISOP, factors the cover, 
  and replaces the current implementation of the MFFC of the cut by the 
  new factored form if the number of AIG nodes is reduced. Returns the
  number of AIG nodes saved.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRefactor( Abc_Ntk_t * pNtk, Abc_ManRef_t * p )
{
    int fCheck = 1;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Replaces MFFC of the node by the new factored.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeUpdate( Abc_Obj_t * pNode, Vec_Ptr_t * vFanins, Vec_Int_t * vForm, int nGain )
{
    Abc_Obj_t * pNodeNew;
    int nNodesNew, nNodesOld;
    nNodesOld = Abc_NtkNodeNum(pNode->pNtk);
    // create the new structure of nodes
    assert( Vec_PtrSize(vFanins) < Vec_IntSize(vForm) );
    pNodeNew = Abc_NodeStrashDec( pNode->pNtk->pManFunc, vFanins, vForm );
    // remove the old nodes
    Abc_AigReplace( pNode->pNtk->pManFunc, pNode, pNodeNew );
    // compare the gains
    nNodesNew = Abc_NtkNodeNum(pNode->pNtk);
    assert( nGain <= nNodesOld - nNodesNew );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


