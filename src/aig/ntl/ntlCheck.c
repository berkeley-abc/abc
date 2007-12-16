/**CFile****************************************************************

  FileName    [ntlCheck.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Checks consistency of the netlist.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntlCheck.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntl.h"
#include "aig.h"

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
int Ntl_ManCheck( Ntl_Man_t * pMan )
{
    // check that the models have unique names
    // check that the models (except the first one) do not have boxes
    return 1;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ModelCheck( Ntl_Mod_t * pModel )
{
    return 1;
}


/**Function*************************************************************

  Synopsis    [Reads the verilog file.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ModelFixNonDrivenNets( Ntl_Mod_t * pModel )
{ 
    Vec_Ptr_t * vNets;
    Ntl_Net_t * pNet;
    Ntl_Obj_t * pNode;
    int i;

    if ( Ntl_ModelIsBlackBox(pModel) )
        return;

    // check for non-driven nets
    vNets = Vec_PtrAlloc( 100 );
    Ntl_ModelForEachNet( pModel, pNet, i )
    {
        if ( pNet->pDriver != NULL )
            continue;
        // add the constant 0 driver
        pNode = Ntl_ModelCreateNode( pModel, 0 );
        pNode->pSop = Ntl_ManStoreSop( pModel->pMan, " 0\n" );
        Ntl_ModelSetNetDriver( pNode, pNet );
        // add the net to those for which the warning will be printed
        Vec_PtrPush( vNets, pNet );
    }

    // print the warning
    if ( Vec_PtrSize(vNets) > 0 )
    {
        printf( "Warning: Constant-0 drivers added to %d non-driven nets in network \"%s\":\n", Vec_PtrSize(vNets), pModel->pName );
        Vec_PtrForEachEntry( vNets, pNet, i )
        {
            printf( "%s%s", (i? ", ": ""), pNet->pName );
            if ( i == 3 )
            {
                if ( Vec_PtrSize(vNets) > 3 )
                    printf( " ..." );
                break;
            }
        }
        printf( "\n" );
    }
    Vec_PtrFree( vNets );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


