/**CFile****************************************************************

  FileName    [abcSeq.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcSeq.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Abc_Obj_t * Abc_NodeSeqToLogic( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pFanin, int nLatches, int Init );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Converts a sequential AIG into a logic SOP network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkSeqToLogicSop( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkNew; 
    Abc_Obj_t * pObj, * pObjNew, * pFaninNew;
    Vec_Ptr_t * vCutset;
    char Buffer[100];
    int i, Init, nDigits;
    assert( Abc_NtkIsSeq(pNtk) );
    // start the network
    vCutset = pNtk->vLats;  pNtk->vLats = Vec_PtrAlloc( 0 );
    pNtkNew = Abc_NtkStartFrom( pNtk, ABC_TYPE_LOGIC, ABC_FUNC_SOP );
    Vec_PtrFree( pNtk->vLats );  pNtk->vLats = vCutset;
    // create the constant node
    Abc_NtkDupConst1( pNtk, pNtkNew );
    // duplicate the nodes, create node functions and latches
    Abc_AigForEachAnd( pNtk, pObj, i )
    {
        Abc_NtkDupObj(pNtkNew, pObj);
        pObj->pCopy->pData = Abc_SopCreateAnd2( pNtkNew->pManFunc, Abc_ObjFaninC0(pObj), Abc_ObjFaninC1(pObj) );
    }
    // connect the objects
    Abc_AigForEachAnd( pNtk, pObj, i )
    {
        // get the initial states of the latches on the fanin edge of this node
        Init = Vec_IntEntry( pNtk->vInits, pObj->Id );
        // create the edge
        pFaninNew = Abc_NodeSeqToLogic( pNtkNew, Abc_ObjFanin0(pObj), Abc_ObjFaninL0(pObj), Init & 0xFFFF );
        Abc_ObjAddFanin( pObj->pCopy, pFaninNew );
        // create the edge
        pFaninNew = Abc_NodeSeqToLogic( pNtkNew, Abc_ObjFanin1(pObj), Abc_ObjFaninL1(pObj), Init >> 16 );
        Abc_ObjAddFanin( pObj->pCopy, pFaninNew );
        // the complemented edges are subsumed by node function
    }
    // set the complemented attributed of CO edges (to be fixed by making simple COs)
    Abc_NtkForEachPo( pNtk, pObj, i )
    {
        // get the initial states of the latches on the fanin edge of this node
        Init = Vec_IntEntry( pNtk->vInits, pObj->Id );
        // create the edge
        pFaninNew = Abc_NodeSeqToLogic( pNtkNew, Abc_ObjFanin0(pObj), Abc_ObjFaninL0(pObj), Init & 0xFFFF );
        Abc_ObjAddFanin( pObj->pCopy, pFaninNew );
        // create the complemented edge
        if ( Abc_ObjFaninC0(pObj) )
            Abc_ObjSetFaninC( pObj->pCopy, 0 );
    }
    // count the number of digits in the latch names
    nDigits = Extra_Base10Log( Abc_NtkLatchNum(pNtkNew) );
    // add the latches and their names
    Abc_NtkForEachLatch( pNtkNew, pObjNew, i )
    {
        // add the latch to the CI/CO arrays
        Vec_PtrPush( pNtkNew->vCis, pObjNew );
        Vec_PtrPush( pNtkNew->vCos, pObjNew );
        // create latch name
        sprintf( Buffer, "L%0*d", nDigits, i );
        Abc_NtkLogicStoreName( pObjNew, Buffer );
    }
    // fix the problem with complemented and duplicated CO edges
    Abc_NtkLogicMakeSimpleCos( pNtkNew, 0 );
    // duplicate the EXDC network
    if ( pNtk->pExdc )
        fprintf( stdout, "Warning: EXDC network is not copied.\n" );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkSeqToLogic(): Network check has failed.\n" );
    return pNtkNew;
}


/**Function*************************************************************

  Synopsis    [Creates latches on one edge.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeSeqToLogic( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pFanin, int nLatches, int Init )
{
    Abc_Obj_t * pLatch;
    if ( nLatches == 0 )
        return pFanin->pCopy;
    pFanin = Abc_NodeSeqToLogic( pNtkNew, pFanin, nLatches - 1, Init >> 2 );
    pLatch = Abc_NtkCreateLatch( pNtkNew );
    pLatch->pData = (void *)(Init & 3);
    Abc_ObjAddFanin( pLatch, pFanin );
    return pLatch;    
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


