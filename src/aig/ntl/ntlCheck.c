/**CFile****************************************************************

  FileName    [ntlCheck.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Checks consistency of the netlist.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntlCheck.c,v 1.1 2008/10/10 14:09:29 mjarvin Exp $]

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
int Ntl_ModelCheckCombPoPaths_rec( Ntl_Mod_t * pModel, Ntl_Net_t * pNet )
{
    Ntl_Net_t * pFanin;
    int i;
    // skip visited nets
    if ( pNet->nVisits == 2 ) 
        return 1;
    pNet->nVisits = 2;
    // process PIs
    if ( Ntl_ObjIsPi(pNet->pDriver) )
        return 0;
    // process registers
    if ( Ntl_ObjIsLatch(pNet->pDriver) )
        return 1;
    assert( Ntl_ObjIsNode(pNet->pDriver) );
    // call recursively
    Ntl_ObjForEachFanin( pNet->pDriver, pFanin, i )
        if ( !Ntl_ModelCheckCombPoPaths_rec( pModel, pFanin ) )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks the existence of combinational paths from POs to PIs.]

  Description [Returns 0 if the path is found.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ModelCheckCombPoPaths( Ntl_Mod_t * pModel )
{
    Ntl_Obj_t * pObj;
    int i;
    Ntl_ModelClearNets( pModel );
    Ntl_ModelForEachPo( pModel, pObj, i )
        if ( !Ntl_ModelCheckCombPoPaths_rec( pModel, Ntl_ObjFanin0(pObj) ) )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks one model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ModelCheck( Ntl_Mod_t * pModel, int fMain )
{
    Ntl_Obj_t * pObj;
    Ntl_Net_t * pNet;
    int i, k, fStatus = 1;

    // check root level model
    if ( fMain )
    {
        if ( Ntl_ModelLatchNum(pModel) > 0 )
        {
            printf( "Root level model %s has %d registers.\n", pModel->pName, Ntl_ModelLatchNum(pModel) );
            fStatus = 0;
        }
        goto checkobjs;
    }

    // check delay information
    if ( pModel->attrBox && pModel->attrComb )
    {
        if ( pModel->vDelays == NULL )
        {
            printf( "Warning: Comb model %s does not have delay info. Default 1.0 delays are assumed.\n", pModel->pName );
            pModel->vDelays = Vec_IntAlloc( 3 );
            Vec_IntPush( pModel->vDelays, -1 );
            Vec_IntPush( pModel->vDelays, -1 );
            Vec_IntPush( pModel->vDelays, Aig_Float2Int(1.0) );        
        }
        if ( pModel->vTimeInputs != NULL )
        {
            printf( "Combinational model %s has input arrival/required time information.\n", pModel->pName );
            fStatus = 0;
        }
        if ( pModel->vTimeOutputs != NULL )
        {
            printf( "Combinational model %s has output arrival/required time information.\n", pModel->pName );
            fStatus = 0;
        }
    }
    if ( pModel->attrBox && !pModel->attrComb )
    {
        if ( pModel->vDelays != NULL )
        {
            printf( "Sequential model %s has delay info.\n", pModel->pName );
            fStatus = 0;
        }
        if ( pModel->vTimeInputs == NULL )
        {
            printf( "Warning: Seq model %s does not have input arrival/required time info. Default 0.0 is assumed.\n", pModel->pName );
            pModel->vTimeInputs = Vec_IntAlloc( 2 );
            Vec_IntPush( pModel->vTimeInputs, -1 );
            Vec_IntPush( pModel->vTimeInputs, Aig_Float2Int(0.0) );        
        }
        if ( pModel->vTimeOutputs == NULL )
        {
//            printf( "Warning: Seq model %s does not have output arrival/required time info. Default 0.0 is assumed.\n", pModel->pName );
            pModel->vTimeOutputs = Vec_IntAlloc( 2 );
            Vec_IntPush( pModel->vTimeOutputs, -1 );
            Vec_IntPush( pModel->vTimeOutputs, Aig_Float2Int(0.0) );        
        }
    }

    // check box attributes
    if ( pModel->attrBox )
    {
        if ( !pModel->attrWhite )
        {
            if ( Ntl_ModelNodeNum(pModel) + Ntl_ModelLut1Num(pModel) > 0 )
            {
                printf( "Model %s is a blackbox, yet it has %d nodes.\n", pModel->pName, Ntl_ModelNodeNum(pModel) + Ntl_ModelLut1Num(pModel) );
                fStatus = 0;
            }
            if ( Ntl_ModelLatchNum(pModel) > 0 )
            {
                printf( "Model %s is a blackbox, yet it has %d registers.\n", pModel->pName, Ntl_ModelLatchNum(pModel) );
                fStatus = 0;
            }
            return fStatus;
        }
        // this is a white box
        if ( pModel->attrComb && Ntl_ModelNodeNum(pModel) + Ntl_ModelLut1Num(pModel) == 0 )
        {
            printf( "Model %s is a comb white box, yet it has no nodes.\n", pModel->pName );
            fStatus = 0;
        }
        if ( pModel->attrComb && Ntl_ModelLatchNum(pModel) > 0 )
        {
            printf( "Model %s is a comb white box, yet it has registers.\n", pModel->pName );
            fStatus = 0;
        }
        if ( !pModel->attrComb && Ntl_ModelLatchNum(pModel) == 0 )
        {
            printf( "Model %s is a seq white box, yet it has no registers.\n", pModel->pName );
            fStatus = 0;
        }
        if ( !pModel->attrComb && !Ntl_ModelCheckCombPoPaths(pModel) )
        {
            printf( "Model %s is a seq white box with comb paths from PIs to POs.\n", pModel->pName );
            fStatus = 0;
        }
    }

checkobjs:
    // check nets
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

    // check objects
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
    Ntl_Mod_t * pMod1;
    int i, fStatus = 1;
    // check that the models have unique names
    Ntl_ManForEachModel( pMan, pMod1, i )
    {
        if ( pMod1->pName == NULL )
        {
            printf( "Model %d does not have a name\n", i );
            fStatus = 0;
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
        if ( !Ntl_ModelCheck( pMod1, i==0 ) )
            fStatus = 0;
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

    if ( !pModel->attrWhite )
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

#if 0  // sjang
    // print the warning
    if ( Vec_PtrSize(vNets) > 0 )
    {
        printf( "Warning: Constant-0 drivers added to %d non-driven nets in network \"%s\": ", Vec_PtrSize(vNets), pModel->pName );
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
#endif
    Vec_PtrFree( vNets );
}

/**Function*************************************************************

  Synopsis    [Fixed problems with non-driven nets in the model.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ModelTransformLatches( Ntl_Mod_t * pModel )
{ 
    Ntl_Mod_t * pMod[3] = { NULL };
    Ntl_Obj_t * pLatch;
    int i, Init;
    if ( Ntl_ModelLatchNum(pModel) == 0 )
        return;
    Ntl_ModelForEachLatch( pModel, pLatch, i )
    {
        Init = pLatch->LatchId.regInit;
        if ( pMod[Init] == NULL )
            pMod[Init] = Ntl_ManCreateLatchModel( pModel->pMan, Init );
        pLatch->pImplem = pMod[Init];
        pLatch->Type = NTL_OBJ_BOX;
    }
    printf( "In the main model \"%s\", %d latches are transformed into white seq boxes.\n", pModel->pName, Ntl_ModelLatchNum(pModel) );
    pModel->nObjs[NTL_OBJ_BOX] += Ntl_ModelLatchNum(pModel);
    pModel->nObjs[NTL_OBJ_LATCH] = 0;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


