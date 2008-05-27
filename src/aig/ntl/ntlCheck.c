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

  Synopsis    [Checks one model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ModelCheck( Ntl_Mod_t * pModel )
{
    Ntl_Obj_t * pObj;
    Ntl_Net_t * pNet;
    int i, k, fStatus = 1;
    Ntl_ModelForEachNet( pModel, pNet, i )
    {
        if ( pNet->pName == NULL )
        {
            printf( "Net in bin %d does not have a name\n", i );
            fStatus = 0;
        }
        if ( pNet->pDriver == NULL )
        {
            printf( "Net %s does not have a driver\n", pNet->pName );
            fStatus = 0;
        }
    }
    Ntl_ModelForEachObj( pModel, pObj, i )
    {
        Ntl_ObjForEachFanin( pObj, pNet, k )
            if ( pNet == NULL )
            {
                printf( "Object %d does not have fanin net %d\n", i, k );
                fStatus = 0;
            }
        Ntl_ObjForEachFanout( pObj, pNet, k )
            if ( pNet == NULL )
            {
                printf( "Object %d does not have fanout net %d\n", i, k );
                fStatus = 0;
            }
    }
    return fStatus;
}

/**Function*************************************************************

  Synopsis    [Checks the netlist.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManCheck( Ntl_Man_t * pMan )
{
    Ntl_Mod_t * pMod1, * pMod2;
    int i, k, fStatus = 1;
    // check that the models have unique names
    Ntl_ManForEachModel( pMan, pMod1, i )
    {
        if ( pMod1->pName == NULL )
        {
            printf( "Model %d does not have a name\n", i );
            fStatus = 0;
        }
        Ntl_ManForEachModel( pMan, pMod2, k )
        {
            if ( i >= k )
                continue;
            if ( strcmp(pMod1->pName, pMod2->pName) == 0 )
            {
                printf( "Models %d and %d have the same name (%s).\n", i, k, pMod1->pName );
                fStatus = 0;
            }
        }
    }
    // check that the models (except the first one) do not have boxes
    Ntl_ManForEachModel( pMan, pMod1, i )
    {
        if ( i == 0 )
            continue;
        if ( Ntl_ModelBoxNum(pMod1) > 0 )
        {
            printf( "Non-root model %d (%s) has %d boxes.\n", i, pMod1->pName, Ntl_ModelBoxNum(pMod1) );
            fStatus = 0;
        }
    }
    // check models
    Ntl_ManForEachModel( pMan, pMod1, i )
    {
        if ( !Ntl_ModelCheck( pMod1 ) )
            fStatus = 0;
        break;
    }
    return fStatus;
}


/**Function*************************************************************

  Synopsis    [Fixed problems with non-driven nets in the model.]

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
        pNode->pSop = Ntl_ManStoreSop( pModel->pMan->pMemSops, " 0\n" );
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


