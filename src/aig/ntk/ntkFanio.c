/**CFile****************************************************************

  FileName    [ntkFanio.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Manipulation of fanins/fanouts.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntkFanio.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntk.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns 1 if it is an AIG with choice nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_ObjCollectFanins( Ntk_Obj_t * pNode, Vec_Ptr_t * vNodes )
{
    Ntk_Obj_t * pFanin;
    int i;
    Vec_PtrClear(vNodes);
    Ntk_ObjForEachFanin( pNode, pFanin, i )
        Vec_PtrPush( vNodes, pFanin );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if it is an AIG with choice nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_ObjCollectFanouts( Ntk_Obj_t * pNode, Vec_Ptr_t * vNodes )
{
    Ntk_Obj_t * pFanout;
    int i;
    Vec_PtrClear(vNodes);
    Ntk_ObjForEachFanout( pNode, pFanout, i )
        Vec_PtrPush( vNodes, pFanout );
}

/**Function*************************************************************

  Synopsis    [Returns the number of the fanin of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntk_ObjFindFanin( Ntk_Obj_t * pObj, Ntk_Obj_t * pFanin )
{  
    Ntk_Obj_t * pTemp;
    int i;
    Ntk_ObjForEachFanin( pObj, pTemp, i )
        if ( pTemp == pFanin )
            return i;
    return -1;
}

/**Function*************************************************************

  Synopsis    [Returns the number of the fanin of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntk_ObjFindFanout( Ntk_Obj_t * pObj, Ntk_Obj_t * pFanout )
{  
    Ntk_Obj_t * pTemp;
    int i;
    Ntk_ObjForEachFanout( pObj, pTemp, i )
        if ( pTemp == pFanout )
            return i;
    return -1;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the object has to be reallocated.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Ntk_ObjReallocIsNeeded( Ntk_Obj_t * pObj )
{  
    return pObj->nFanins + pObj->nFanouts == (unsigned)pObj->nFanioAlloc;
}

/**Function*************************************************************

  Synopsis    [Deletes the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static Ntk_Obj_t * Ntk_ManReallocNode( Ntk_Obj_t * pObj )
{  
    Ntk_Obj_t * pObjNew, * pTemp;
    int i, iNum;
    assert( Ntk_ObjReallocIsNeeded(pObj) );
    pObjNew = (Ntk_Obj_t *)Aig_MmFlexEntryFetch( pObj->pMan->pMemObjs, sizeof(Ntk_Obj_t) + 2 * pObj->nFanioAlloc * sizeof(Ntk_Obj_t *) );
    memmove( pObjNew, pObj, sizeof(Ntk_Obj_t) + pObj->nFanioAlloc * sizeof(Ntk_Obj_t *) );
    pObjNew->nFanioAlloc = pObj->nFanioAlloc;
    // update the fanouts' fanins
    Ntk_ObjForEachFanout( pObj, pTemp, i )
    {
        iNum = Ntk_ObjFindFanin( pTemp, pObj );
        if ( iNum == -1 )
            printf( "Ntk_ManReallocNode(): Error! Fanin cannot be found.\n" );
        pTemp->pFanio[iNum] = pObjNew;
    }
    // update the fanins' fanouts
    Ntk_ObjForEachFanin( pObj, pTemp, i )
    {
        iNum = Ntk_ObjFindFanout( pTemp, pObj );
        if ( iNum == -1 )
            printf( "Ntk_ManReallocNode(): Error! Fanout cannot be found.\n" );
        pTemp->pFanio[pTemp->nFanins+iNum] = pObjNew;
    }
    return pObjNew;
}


/**Function*************************************************************

  Synopsis    [Creates fanout/fanin relationship between the nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_ObjAddFanin( Ntk_Obj_t * pObj, Ntk_Obj_t * pFanin )
{
    int i;
    assert( pObj->pMan == pFanin->pMan );
    assert( pObj->Id >= 0 && pFanin->Id >= 0 );
    if ( Ntk_ObjReallocIsNeeded(pObj) )
        Ntk_ManReallocNode( pObj );
    if ( Ntk_ObjReallocIsNeeded(pFanin) )
        Ntk_ManReallocNode( pFanin );
    for ( i = pObj->nFanins + pObj->nFanouts; i > (int)pObj->nFanins; i-- )
        pObj->pFanio[i] = pObj->pFanio[i-1];
    pObj->pFanio[pObj->nFanins++] = pFanin;
    pFanin->pFanio[pFanin->nFanins + pFanin->nFanouts++] = pObj;
}

/**Function*************************************************************

  Synopsis    [Removes fanout/fanin relationship between the nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_ObjDeleteFanin( Ntk_Obj_t * pObj, Ntk_Obj_t * pFanin )
{
    int i, k, Limit;
    // remove pFanin from the fanin list of pObj
    Limit = pObj->nFanins + pObj->nFanouts;
    for ( k = i = 0; i < Limit; i++ )
        if ( pObj->pFanio[i] != pFanin )
            pObj->pFanio[k++] = pObj->pFanio[i];
    pObj->nFanins--;
    // remove pObj from the fanout list of pFanin
    Limit = pFanin->nFanins + pFanin->nFanouts;
    for ( k = i = pFanin->nFanins; i < Limit; i++ )
        if ( pFanin->pFanio[i] != pObj )
            pFanin->pFanio[k++] = pFanin->pFanio[i];
    pFanin->nFanouts--;
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
void Ntk_ObjPatchFanin( Ntk_Obj_t * pObj, Ntk_Obj_t * pFaninOld, Ntk_Obj_t * pFaninNew )
{
    int i, k, iFanin, Limit;
    assert( pFaninOld != pFaninNew );
    assert( pObj != pFaninOld );
    assert( pObj != pFaninNew );
    assert( pObj->pMan == pFaninOld->pMan );
    assert( pObj->pMan == pFaninNew->pMan );
    // update the fanin
    iFanin = Ntk_ObjFindFanin( pObj, pFaninOld );
    if ( iFanin == -1 )
    {
        printf( "Ntk_ObjPatchFanin(); Error! Node %d is not among", pFaninOld->Id );
        printf( " the fanins of node %s...\n", pObj->Id );
        return;
    }
    pObj->pFanio[iFanin] = pFaninNew;
    // remove pObj from the fanout list of pFaninOld
    Limit = pFaninOld->nFanins + pFaninOld->nFanouts;
    for ( k = i = pFaninOld->nFanins; i < Limit; i++ )
        if ( pFaninOld->pFanio[i] != pObj )
            pFaninOld->pFanio[k++] = pFaninOld->pFanio[i];
    pFaninOld->nFanouts--;
    // add pObj to the fanout list of pFaninNew
    if ( Ntk_ObjReallocIsNeeded(pFaninNew) )
        Ntk_ManReallocNode( pFaninNew );
    pFaninNew->pFanio[pFaninNew->nFanins + pFaninNew->nFanouts++] = pObj;
}


/**Function*************************************************************

  Synopsis    [Transfers fanout from the old node to the new node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_ObjTransferFanout( Ntk_Obj_t * pNodeFrom, Ntk_Obj_t * pNodeTo )
{
    Vec_Ptr_t * vFanouts = pNodeFrom->pMan->vTemp;
    Ntk_Obj_t * pTemp;
    int nFanoutsOld, i;
    assert( !Ntk_ObjIsCo(pNodeFrom) && !Ntk_ObjIsCo(pNodeTo) );
    assert( pNodeFrom->pMan == pNodeTo->pMan );
    assert( pNodeFrom != pNodeTo );
    assert( Ntk_ObjFanoutNum(pNodeFrom) > 0 );
    // get the fanouts of the old node
    nFanoutsOld = Ntk_ObjFanoutNum(pNodeTo);
    Ntk_ObjCollectFanouts( pNodeFrom, vFanouts );
    // patch the fanin of each of them
    Vec_PtrForEachEntry( vFanouts, pTemp, i )
        Ntk_ObjPatchFanin( pTemp, pNodeFrom, pNodeTo );
    assert( Ntk_ObjFanoutNum(pNodeFrom) == 0 );
    assert( Ntk_ObjFanoutNum(pNodeTo) == nFanoutsOld + Vec_PtrSize(vFanouts) );
}

/**Function*************************************************************

  Synopsis    [Replaces the node by a new node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_ObjReplace( Ntk_Obj_t * pNodeOld, Ntk_Obj_t * pNodeNew )
{
    assert( pNodeOld->pMan == pNodeNew->pMan );
    assert( pNodeOld != pNodeNew );
    assert( Ntk_ObjFanoutNum(pNodeOld) > 0 );
    // transfer the fanouts to the old node
    Ntk_ObjTransferFanout( pNodeOld, pNodeNew );
    // remove the old node
    Ntk_ManDeleteNode_rec( pNodeOld );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


