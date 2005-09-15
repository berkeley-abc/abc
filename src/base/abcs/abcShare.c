/**CFile****************************************************************

  FileName    [abcShare.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Procedures for latch sharing on the fanout edges.]

  Synopsis    [Utilities working sequential AIGs.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcShare.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abcs.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Abc_NodeSeqShareFanouts( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes );
static void Abc_NodeSeqShareOne( Abc_Obj_t * pNode, Abc_InitType_t Init, Vec_Ptr_t * vNodes );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Transforms the sequential AIG to take fanout sharing into account.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkSeqShareFanouts( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pObj;
    int i;
    vNodes = Vec_PtrAlloc( 10 );
    Abc_NtkForEachNode( pNtk, pObj, i )
        Abc_NodeSeqShareFanouts( pObj, vNodes );
    Vec_PtrFree( vNodes );
}

/**Function*************************************************************

  Synopsis    [Transforms the node to take fanout sharing into account.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeSeqShareFanouts( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes )
{
    Abc_Obj_t * pFanout;
    Abc_InitType_t Type;
    int nLatches[4], i;
    // skip the node with only one fanout
    if ( Abc_ObjFanoutNum(pNode) < 2 )
        return;
    // clean the the fanout counters
    for ( i = 0; i < 4; i++ )
        nLatches[i] = 0;
    // find the number of fanouts having latches of each type
    Abc_ObjForEachFanout( pNode, pFanout, i )  
    {
        if ( Abc_ObjFanoutL(pNode, pFanout) == 0 )
            continue;
        Type = Abc_ObjFaninLGetInitLast( pFanout, Abc_ObjEdgeNum(pNode, pFanout) );
        nLatches[Type]++;
    }
    // decide what to do
    if ( nLatches[ABC_INIT_ZERO] > 1 && nLatches[ABC_INIT_ONE] > 1 ) // 0-group and 1-group
    {
        Abc_NodeSeqShareOne( pNode, ABC_INIT_ZERO, vNodes );     // shares 0 and DC
        Abc_NodeSeqShareOne( pNode, ABC_INIT_ONE,  vNodes );     // shares 1 and DC
    }
    else if ( nLatches[ABC_INIT_ZERO] > 1 ) // 0-group
        Abc_NodeSeqShareOne( pNode, ABC_INIT_ZERO, vNodes );     // shares 0 and DC
    else if ( nLatches[ABC_INIT_ONE] > 1 ) // 1-group
        Abc_NodeSeqShareOne( pNode, ABC_INIT_ONE,  vNodes );     // shares 1 and DC
    else if ( nLatches[ABC_INIT_DC] > 1 ) // DC-group
    {
        if ( nLatches[ABC_INIT_ZERO] > 0 )
            Abc_NodeSeqShareOne( pNode, ABC_INIT_ZERO, vNodes ); // shares 0 and DC
        else 
            Abc_NodeSeqShareOne( pNode, ABC_INIT_ONE,  vNodes ); // shares 1 and DC
    }
}

/**Function*************************************************************

  Synopsis    [Transforms the node to take fanout sharing into account.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeSeqShareOne( Abc_Obj_t * pNode, Abc_InitType_t Init, Vec_Ptr_t * vNodes )
{
    Vec_Int_t * vInits = pNode->pNtk->vInits;
    Abc_Obj_t * pFanout, * pBuffer;
    Abc_InitType_t Type, InitNew;
    int i;
    // collect the fanouts that satisfy the property (have initial value Init or DC)
    InitNew = ABC_INIT_DC;
    Vec_PtrClear( vNodes );
    Abc_ObjForEachFanout( pNode, pFanout, i )
    {
        if ( Abc_ObjFanoutL(pNode, pFanout) == 0 )
            continue;
        Type = Abc_ObjFaninLGetInitLast( pFanout, Abc_ObjEdgeNum(pNode, pFanout) );
        if ( Type == Init )
            InitNew = Init;
        if ( Type == Init || Type == ABC_INIT_DC )
        {
            Vec_PtrPush( vNodes, pFanout );
            Abc_ObjFaninLDeleteLast( pFanout, Abc_ObjEdgeNum(pNode, pFanout) );
        }
    }
    // create the new buffer
    pBuffer = Abc_NtkCreateNode( pNode->pNtk );
    Abc_ObjAddFanin( pBuffer, pNode );
    Abc_ObjSetFaninL( pBuffer, 0, 1 );
    // add the initial state
    assert( Vec_IntSize(vInits) == 2 * (int)pBuffer->Id );
    Vec_IntPush( vInits, InitNew );
    Vec_IntPush( vInits, 0       );
    // redirect the fanouts
    Vec_PtrForEachEntry( vNodes, pFanout, i )
        Abc_ObjPatchFanin( pFanout, pNode, pBuffer );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


