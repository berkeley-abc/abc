/**CFile****************************************************************

  FileName    [resUpdate.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Resynthesis package.]

  Synopsis    [Updates the network after changes.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - January 15, 2007.]

  Revision    [$Id: resUpdate.c,v 1.00 2007/01/15 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "resInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes the level of the node using its fanin levels.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Res_UpdateNetworkLevelNew( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanin;
    int i, Level = 0;
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Level = ABC_MAX( Level, (int)pFanin->Level );
    return Level + 1;
}

/**Function*************************************************************

  Synopsis    [Incrementally updates level of the nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_UpdateNetworkLevel( Abc_Obj_t * pObjNew, Vec_Vec_t * vLevels )
{
    Abc_Obj_t * pFanout, * pTemp;
    int Lev, k, m;
    // check if level has changed
    if ( (int)pObjNew->Level == Res_UpdateNetworkLevelNew(pObjNew) )
        return;
    // start the data structure for level update
    Vec_VecClear( vLevels );
    Vec_VecPush( vLevels, pObjNew->Level, pObjNew );
    pObjNew->fMarkA = 1;
    // recursively update level
    Vec_VecForEachEntryStart( vLevels, pTemp, Lev, k, pObjNew->Level )
    {
        pTemp->fMarkA = 0;
        pTemp->Level = Res_UpdateNetworkLevelNew( pTemp );
        // if the level did not change, to need to check the fanout levels
        if ( (int)pTemp->Level == Lev )
            continue;
        // schedule fanout for level update
        Abc_ObjForEachFanout( pTemp, pFanout, m )
            if ( !Abc_ObjIsCo(pFanout) && !pFanout->fMarkA )
            {
                Vec_VecPush( vLevels, pFanout->Level, pFanout );
                pFanout->fMarkA = 1;
            }
    }
}

/**Function*************************************************************

  Synopsis    [Incrementally updates level of the nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Res_UpdateNetwork( Abc_Obj_t * pObj, Vec_Ptr_t * vFanins, Hop_Obj_t * pFunc, Vec_Vec_t * vLevels )
{
    Abc_Obj_t * pObjNew, * pFanin;
    int k;
    // create the new node
    pObjNew = Abc_NtkCreateNode( pObj->pNtk );
    pObjNew->pData = pFunc;
    Vec_PtrForEachEntry( vFanins, pFanin, k )
        Abc_ObjAddFanin( pObjNew, pFanin );
    // replace the old node by the new node
    pObjNew->Level = pObj->Level;
    Abc_ObjReplace( pObj, pObjNew );
    // update the level of the node
    Res_UpdateNetworkLevel( pObjNew, vLevels );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


