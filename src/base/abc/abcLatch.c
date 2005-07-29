/**CFile****************************************************************

  FileName    [abcLatch.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Procedures working with latches.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcLatch.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Checks whether the network is combinational.]

  Description [The network is combinational if it has no latches.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkIsComb( Abc_Ntk_t * pNtk )
{
    return pNtk->vLatches->nSize == 0;
}

/**Function*************************************************************

  Synopsis    [Makes the network combinational.]

  Description [If the network is sequential, the latches are disconnected,
  while the latch inputs and outputs are added to the PIs and POs.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkMakeComb( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pLatch, * pNet;
    int i;

    if ( !Abc_NtkIsNetlist(pNtk) )
        return 0;

    // skip if the network is already combinational
    if ( Abc_NtkIsComb( pNtk ) )
        return 0;

    // save the number of PIs/POs
    assert( pNtk->nPisOld == 0 );
    assert( pNtk->nPosOld == 0 );
    pNtk->nPisOld = pNtk->vPis->nSize;
    pNtk->nPosOld = pNtk->vPos->nSize;
    if ( Abc_NtkIsNetlist(pNtk) )
    {
        // go through the latches
        // - disconnect LO/LI nets from latches
        // - add them to the PI/PO lists
        Abc_NtkForEachLatch( pNtk, pLatch, i )
        {
            // process the input of the latch
            pNet = Abc_ObjFanin0( pLatch );
            assert( Abc_ObjIsLi( pNet ) );
            if ( !Vec_FanDeleteEntry( &pNet->vFanouts, pLatch->Id ) )
            {
                printf( "Abc_NtkMakeComb: The latch is not found among the fanouts of the fanin net...\n" );
                return 0;
            }
            if ( !Abc_ObjIsPo( pNet ) )
                Abc_NtkMarkNetPo( pNet );

            // process the output of the latch
            pNet = Abc_ObjFanout0( pLatch );
            assert( Abc_ObjIsLo( pNet ) );
            if ( !Vec_FanDeleteEntry( &pNet->vFanins, pLatch->Id ) )
            {
                printf( "Abc_NtkMakeComb: The latch is not found among the fanins of the fanout net...\n" );
                return 0;
            }
            assert( !Abc_ObjIsPi( pNet ) );
            Abc_NtkMarkNetPi( pNet );
        }
    }
    else
    {
        assert( 0 );
/*
        // go through the latches and add them to PIs and POs
        Abc_NtkForEachLatch( pNtk, pLatch, i )
        {
//            pLatch->Type = ABC_OBJ_TYPE_NODE;
            Vec_PtrPush( pNtk->vPis, pLatch );
            Vec_PtrPush( pNtk->vPos, pLatch );
            // add the names of the latches to the names of the PIs
            Vec_PtrPush( pNtk->vNamesPi, pNtk->vNamesLatch->pArray[i] );
        }
*/
    }
    // save the latches in the backup place
    pNtk->vLatches2 = pNtk->vLatches;
    pNtk->vLatches  = Vec_PtrAlloc( 0 );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Makes the network sequential again.]

  Description [If the network was made combinational by disconnecting 
  latches, this procedure makes it sequential again.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkMakeSeq( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pLatch, * pNet;
    int i;

    if ( !Abc_NtkIsNetlist(pNtk) )
        return 0;

    // skip if the network has no latches
    if ( pNtk->vLatches2 == NULL || pNtk->vLatches2->nSize == 0 )
        return 0;
    // move the latches from the backup place
    Vec_PtrFree( pNtk->vLatches );
    pNtk->vLatches = pNtk->vLatches2;
    pNtk->vLatches2 = NULL;
    if ( Abc_NtkIsNetlist(pNtk) )
    {
        // go through the latches and connect the LI/LO nets back to the latches
        Abc_NtkForEachLatch( pNtk, pLatch, i )
        {
            // process the input of the latch
            pNet = Abc_ObjFanin0( pLatch );
            assert( Abc_ObjIsLi( pNet ) );
            Vec_FanPush( pNtk->pMmStep, &pNet->vFanouts, Vec_Int2Fan(pLatch->Id) );
            // process the output of the latch
            pNet = Abc_ObjFanout0( pLatch );
            assert( Abc_ObjIsLo( pNet ) );
            Vec_FanPush( pNtk->pMmStep, &pNet->vFanins, Vec_Int2Fan(pLatch->Id) );
        }
        // clean the PI/PO attributes of the former latch variables
        for ( i = pNtk->nPisOld; i < pNtk->vPis->nSize; i++ )
            Abc_ObjUnsetSubtype( Abc_NtkPi(pNtk, i), ABC_OBJ_SUBTYPE_PI );
        for ( i = pNtk->nPosOld; i < pNtk->vPos->nSize; i++ )
            Abc_ObjUnsetSubtype( Abc_NtkPo(pNtk, i), ABC_OBJ_SUBTYPE_PO );
    }
    else
    {
        assert( 0 );
//        Vec_PtrShrink( pNtk->vNamesPi, pNtk->nPisOld );
    }
    // remove the nodes from the PI/PO lists
    Vec_PtrShrink( pNtk->vPis, pNtk->nPisOld );
    Vec_PtrShrink( pNtk->vPos, pNtk->nPosOld );
    pNtk->nPis = pNtk->vPis->nSize;
    pNtk->nPos = pNtk->vPos->nSize;
    pNtk->nPisOld = 0;
    pNtk->nPosOld = 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks if latches form self-loop.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkLatchIsSelfFeed_rec( Abc_Obj_t * pLatch, Abc_Obj_t * pLatchRoot )
{
    Abc_Obj_t * pFanin;
    assert( Abc_ObjIsLatch(pLatch) );
    if ( pLatch == pLatchRoot )
        return 1;
    pFanin = Abc_ObjFanin0(pLatch);
    if ( !Abc_ObjIsLatch(pFanin) )
        return 0;
    return Abc_NtkLatchIsSelfFeed_rec( pFanin, pLatch );
}

/**Function*************************************************************

  Synopsis    [Checks if latches form self-loop.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NtkLatchIsSelfFeed( Abc_Obj_t * pLatch )
{
    Abc_Obj_t * pFanin;
    assert( Abc_ObjIsLatch(pLatch) );
    pFanin = Abc_ObjFanin0(pLatch);
    if ( !Abc_ObjIsLatch(pFanin) )
        return 0;
    return Abc_NtkLatchIsSelfFeed_rec( pFanin, pLatch );
}

/**Function*************************************************************

  Synopsis    [Checks if latches form self-loop.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkCountSelfFeedLatches( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pLatch;
    int i, Counter;
    Counter = 0;
    Abc_NtkForEachLatch( pNtk, pLatch, i )
        Counter += Abc_NtkLatchIsSelfFeed( pLatch );
    return Counter;
}



////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


