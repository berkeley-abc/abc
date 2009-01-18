/**CFile****************************************************************

  FileName    [ntlSweep.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Performs structural sweep of the netlist.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntlSweep.c,v 1.1 2008/10/10 14:09:30 mjarvin Exp $]

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
    // start from the persistant boxes
    Ntl_ModelForEachBox( pRoot, pObj, i )
        if ( pObj->pImplem->attrKeep )
            Ntl_ManSweepMark_rec( p, pObj );
}

/**Function*************************************************************

  Synopsis    [Removes logic that does not fanout into POs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManSweep( Ntl_Man_t * p, int fVerbose )
{
    int nObjsOld[NTL_OBJ_VOID];
    Ntl_Mod_t * pRoot, * pMod;
    Ntl_Net_t * pNet;
    Ntl_Obj_t * pObj;
    int i, k, nNetsOld;
    int ModelCounter = 0, Counter = 0;

    // remember the number of objects
    pRoot = Ntl_ManRootModel( p );
    for ( i = 0; i < NTL_OBJ_VOID; i++ )
        nObjsOld[i] = pRoot->nObjs[i];
    nNetsOld = Ntl_ModelCountNets(pRoot);

    // mark the nets that do not fanout into POs
    Ntl_ManSweepMark( p );

    // count how many boxes of each type are swept away
    if ( fVerbose )
    {
    Ntl_ManForEachModel( p, pMod, i )
        pMod->nUsed = pMod->nRems = 0;
    Ntl_ModelForEachObj( pRoot, pObj, i )
        if ( Ntl_ObjIsBox(pObj) && pObj->pImplem )
        {
            pObj->pImplem->nUsed++;
            if ( !pObj->fMark )
            {
                if ( pObj->pImplem->nRems++ == 0 )
                    ModelCounter++;
            }
        }
    }

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
            if ( pNet != NULL && pNet->pName[0] != 0 )
            {
                Ntl_ModelDeleteNet( pRoot, pNet );
                Vec_PtrWriteEntry( pRoot->vNets, pNet->NetId, NULL );
            }
        // remove the object
        if ( Ntl_ObjIsNode(pObj) && Ntl_ObjFaninNum(pObj) == 1 )
            pRoot->nObjs[NTL_OBJ_LUT1]--;
        else 
            pRoot->nObjs[pObj->Type]--;
        Vec_PtrWriteEntry( pRoot->vObjs, pObj->Id, NULL );
        pObj->Type = NTL_OBJ_NONE;
        Counter++;
    }
 


    // print detailed statistics of sweeping
    if ( fVerbose && Counter > 0)
    {
        int numLutBox = 0;

        printf( "Swept away:" );
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
        if ( ModelCounter )
        {
            printf( "Sweep removed %d boxed of %d types (out of %d types):\n", 
                nObjsOld[NTL_OBJ_BOX] - pRoot->nObjs[NTL_OBJ_BOX], ModelCounter, Vec_PtrSize(p->vModels)-1 );
            Ntl_ManForEachModel( p, pMod, i )
            {
                if ( i && (pMod->nRems + pMod->nUsed-pMod->nRems) > 0)
                {

                    if (strncmp(pMod->pName, "LUT", 3) != 0)
                    {
                        //printf( "( M%d: %s,  S=%d, L=%d ) ", i, pMod->pName, pMod->nRems, pMod->nUsed-pMod->nRems );
                        //printf( "Model %3d : %-40s  Swept = %5d. Left = %5d.\n", i, pMod->pName, pMod->nRems, pMod->nUsed-pMod->nRems );
                    } else
                    {
                        numLutBox++;
                    }
                }
            }
//            printf("\nLUTboxType =%d\n", numLutBox);
        }
    }
    if ( !Ntl_ManCheck( p ) )
        printf( "Ntl_ManSweep: The check has failed for design %s.\n", p->pName );
    return Counter;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


