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
#include "rwr.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

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
    Rwr_Man_t * p;
    Abc_Obj_t * pNode;
    int i, nNodes, nGain;

    assert( Abc_NtkIsAig(pNtk) );
    // start the rewriting manager
    p = Rwr_ManStart( 0 );
    if ( p == NULL )
        return 0;
    Rwr_ManPrepareNetwork( p, pNtk );

    // resynthesize each node once
    nNodes = Abc_NtkObjNumMax(pNtk);
    pProgress = Extra_ProgressBarStart( stdout, nNodes );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        // stop if all nodes have been tried once
        if ( i >= nNodes )
            break;
        // skip the constant node
        if ( Abc_NodeIsConst(pNode) )
            continue;
        // for each cut, try to resynthesize it
        if ( (nGain = Rwr_NodeRewrite( p, pNode )) >= 0 )
            Abc_NodeUpdate( pNode, Rwr_ManReadFanins(p), Rwr_ManReadDecs(p), nGain );
    }
    Extra_ProgressBarStop( pProgress );
    // delete the manager
    Rwr_ManStop( p );
    // check
    if ( fCheck && !Abc_NtkCheck( pNtk ) )
    {
        printf( "Abc_NtkRewrite: The network check has failed.\n" );
        return 0;
    }
    return 1;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


