/**CFile****************************************************************

  FileName    [abcFanio.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Various procedures to connect fanins/fanouts.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcFanio.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define ABC_LARGE_ID   ((1<<24)-1)   // should correspond to value in "vecFan.h"

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates fanout/fanin relationship between the nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ObjAddFanin( Abc_Obj_t * pObj, Abc_Obj_t * pFanin )
{
    Abc_Obj_t * pFaninR = Abc_ObjRegular(pFanin);
    assert( !Abc_ObjIsComplement(pObj) );
    assert( pObj->pNtk == pFaninR->pNtk );
    assert( pObj->Id >= 0 && pFaninR->Id >= 0 );
    assert( pObj->Id    < ABC_LARGE_ID );  // created but forgot to add it to the network?
    assert( pFaninR->Id < ABC_LARGE_ID );  // created but forgot to add it to the network?
    Vec_FanPush( pObj->pNtk->pMmStep, &pObj->vFanins,     Vec_Int2Fan(pFaninR->Id) );
    Vec_FanPush( pObj->pNtk->pMmStep, &pFaninR->vFanouts, Vec_Int2Fan(pObj->Id)    );
    if ( Abc_ObjIsComplement(pFanin) )
        Abc_ObjSetFaninC( pObj, Abc_ObjFaninNum(pObj)-1 );
}


/**Function*************************************************************

  Synopsis    [Destroys fanout/fanin relationship between the nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ObjDeleteFanin( Abc_Obj_t * pObj, Abc_Obj_t * pFanin )
{
    assert( !Abc_ObjIsComplement(pObj) );
    assert( !Abc_ObjIsComplement(pFanin) );
    assert( pObj->pNtk == pFanin->pNtk );
    assert( pObj->Id >= 0 && pFanin->Id >= 0 );
    assert( pObj->Id   < ABC_LARGE_ID );  // created but forgot to add it to the network?
    assert( pFanin->Id < ABC_LARGE_ID );  // created but forgot to add it to the network?
    if ( !Vec_FanDeleteEntry( &pObj->vFanins, pFanin->Id ) )
    {
        printf( "The obj %d is not found among the fanins of obj %d ...\n", pFanin->Id, pObj->Id );
        return;
    }
    if ( !Vec_FanDeleteEntry( &pFanin->vFanouts, pObj->Id ) )
    {
        printf( "The obj %d is not found among the fanouts of obj %d ...\n", pObj->Id, pFanin->Id );
        return;
    }
}


/**Function*************************************************************

  Synopsis    [Destroys fanout/fanin relationship between the nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ObjRemoveFanins( Abc_Obj_t * pObj )
{
    Vec_Fan_t * vFaninsOld;
    Abc_Obj_t * pFanin;
    int k;
    // remove old fanins
    vFaninsOld = &pObj->vFanins;
    for ( k = vFaninsOld->nSize - 1; k >= 0; k-- )
    {
        pFanin = Abc_NtkObj( pObj->pNtk, vFaninsOld->pArray[k].iFan );
        Abc_ObjDeleteFanin( pObj, pFanin );
    }
}

/**Function*************************************************************

  Synopsis    [Replaces a fanin of the node.]

  Description [The node is pObj. An old fanin of this node (pFaninOld) has to be
  replaced by a new fanin (pFaninNew). Assumes that the node and the old fanin 
  are not complemented. The new fanin can be complemented. In this case, the
  polarity of the new fanin will change, compared to the polarity of the old fanin.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ObjPatchFanin( Abc_Obj_t * pObj, Abc_Obj_t * pFaninOld, Abc_Obj_t * pFaninNew )
{
    Abc_Obj_t * pFaninNewR = Abc_ObjRegular(pFaninNew);
    int iFanin, fCompl, nLats;
    assert( !Abc_ObjIsComplement(pObj) );
    assert( !Abc_ObjIsComplement(pFaninOld) );
    assert( pFaninOld != pFaninNewR );
//    assert( pObj != pFaninOld );
//    assert( pObj != pFaninNewR );
    assert( pObj->pNtk == pFaninOld->pNtk );
    assert( pObj->pNtk == pFaninNewR->pNtk );
    if ( (iFanin = Vec_FanFindEntry( &pObj->vFanins, pFaninOld->Id )) == -1 )
    {
        printf( "Node %s is not among", Abc_ObjName(pFaninOld) );
        printf( " the fanins of node %s...\n", Abc_ObjName(pObj) );
        return;
    }
    // remember the attributes of the old fanin
    fCompl = Abc_ObjFaninC(pObj, iFanin);
    nLats  = Abc_ObjFaninL(pObj, iFanin);
    // replace the old fanin entry by the new fanin entry (removes attributes)
    Vec_FanWriteEntry( &pObj->vFanins, iFanin, Vec_Int2Fan(pFaninNewR->Id) );
    // set the attributes of the new fanin
    if ( fCompl ^ Abc_ObjIsComplement(pFaninNew) )
        Abc_ObjSetFaninC( pObj, iFanin );
    if ( nLats )
        Abc_ObjSetFaninL( pObj, iFanin, nLats );
    // update the fanout of the fanin
    if ( !Vec_FanDeleteEntry( &pFaninOld->vFanouts, pObj->Id ) )
    {
        printf( "Node %s is not among", Abc_ObjName(pObj) );
        printf( " the fanouts of its old fanin %s...\n", Abc_ObjName(pFaninOld) );
//        return;
    }
    Vec_FanPush( pObj->pNtk->pMmStep, &pFaninNewR->vFanouts, Vec_Int2Fan(pObj->Id) );
}

/**Function*************************************************************

  Synopsis    [Transfers fanout from the old node to the new node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ObjTransferFanout( Abc_Obj_t * pNodeFrom, Abc_Obj_t * pNodeTo )
{
    Vec_Ptr_t * vFanouts = pNodeFrom->pNtk->vPtrTemp;
    int nFanoutsOld, i;
    assert( !Abc_ObjIsComplement(pNodeFrom) );
    assert( !Abc_ObjIsComplement(pNodeTo) );
    assert( Abc_ObjIsNode(pNodeFrom) );
    assert( Abc_ObjIsNode(pNodeTo) );
    assert( pNodeFrom->pNtk == pNodeTo->pNtk );
    assert( pNodeFrom != pNodeTo );
    assert( Abc_ObjFanoutNum(pNodeFrom) > 0 );
    // get the fanouts of the old node
    nFanoutsOld = Abc_ObjFanoutNum(pNodeTo);
    Abc_NodeCollectFanouts( pNodeFrom, vFanouts );
    // patch the fanin of each of them
    for ( i = 0; i < vFanouts->nSize; i++ )
        Abc_ObjPatchFanin( vFanouts->pArray[i], pNodeFrom, pNodeTo );
    assert( Abc_ObjFanoutNum(pNodeFrom) == 0 );
    assert( Abc_ObjFanoutNum(pNodeTo) == nFanoutsOld + vFanouts->nSize );
}

/**Function*************************************************************

  Synopsis    [Replaces the node by a new node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ObjReplace( Abc_Obj_t * pNodeOld, Abc_Obj_t * pNodeNew )
{
    assert( !Abc_ObjIsComplement(pNodeOld) );
    assert( !Abc_ObjIsComplement(pNodeNew) );
    assert( Abc_ObjIsNode(pNodeOld) );
    assert( Abc_ObjIsNode(pNodeNew) );
    assert( pNodeOld->pNtk == pNodeNew->pNtk );
    assert( pNodeOld != pNodeNew );
    assert( Abc_ObjFanoutNum(pNodeOld) > 0 );
    assert( Abc_ObjFanoutNum(pNodeNew) == 0 );
    // transfer the fanouts to the old node
    Abc_ObjTransferFanout( pNodeOld, pNodeNew );
    // remove the old node
    Abc_NtkDeleteObj( pNodeOld );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


