/**CFile****************************************************************

  FileName    [abcSeq.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Procedures to derive sequential AIG from combinational AIG with latches.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcSeq.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

/*
    A sequential network is similar to AIG in that it contains only
    AND gates. However, the AND-gates are currently not hashed. 
    Const1/PIs/POs remain the same as in the original AIG.
    Instead of the latches, a new cutset is added, which is currently
    defined as a set of AND gates that have a latch among their fanouts.
    The edges of a sequential AIG are labeled with latch attributes
    in addition to the complementation attibutes. 
    The attributes contain information about the number of latches 
    and their initial states. 
    The number of latches is stored directly on the edges. The initial 
    states are stored in a special array associated with the network.
    The AIG of sequential network is static in the sense that the 
    new AIG nodes are never created.
    The retiming (or retiming/mapping) is performed by moving the
    latches over the static nodes of the AIG.
    The new initial state after forward retiming is computed in a
    straight-forward manner. After backward retiming it is computed
    by setting up a SAT problem.
*/

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static Vec_Ptr_t * Abc_NtkAigCutsetCopy( Abc_Ntk_t * pNtk );
static Abc_Obj_t * Abc_NodeAigToSeq( Abc_Obj_t * pAnd, int Num, int * pnLatches, int * pnInit );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Converts a normal AIG into a sequential AIG.]

  Description [The const/PI/PO nodes are duplicated. The internal
  nodes are duplicated in the topological order. The dangling nodes
  are not copies. The choice nodes are copied.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkAigToSeq( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkNew;
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pObj, * pFanin0, * pFanin1;
    int i, nLatches0, nLatches1, Init0, Init1;
    // make sure it is an AIG without self-feeding latches
    assert( Abc_NtkIsStrash(pNtk) );
    assert( Abc_NtkCountSelfFeedLatches(pNtk) == 0 );
    // start the network
    pNtkNew = Abc_NtkAlloc( ABC_TYPE_SEQ, ABC_FUNC_AIG );
    // duplicate the name and the spec
    pNtkNew->pName = util_strsav(pNtk->pName);
    pNtkNew->pSpec = util_strsav(pNtk->pSpec);
    // clone const/PIs/POs
    Abc_NtkDupObj(pNtkNew, Abc_AigConst1(pNtk->pManFunc) );
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_NtkDupObj(pNtkNew, pObj);
    Abc_NtkForEachPo( pNtk, pObj, i )
        Abc_NtkDupObj(pNtkNew, pObj);
    // copy the PI/PO names
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_NtkLogicStoreName( Abc_NtkPi(pNtkNew,i), Abc_ObjName(pObj) );
    Abc_NtkForEachPo( pNtk, pObj, i ) 
        Abc_NtkLogicStoreName( Abc_NtkPo(pNtkNew,i), Abc_ObjName(pObj) );
    // copy the internal nodes, including choices, excluding dangling
    vNodes = Abc_AigDfs( pNtk, 0, 0 );
    Vec_PtrForEachEntry( vNodes, pObj, i )
        Abc_NtkDupObj(pNtkNew, pObj);
    Vec_PtrFree( vNodes );
    // start the storage for initial states
    pNtkNew->vInits = Vec_IntStart( Abc_NtkObjNumMax(pNtkNew) );
    // reconnect the internal nodes
    Abc_AigForEachAnd( pNtk, pObj, i )
    {
        // process the fanins of the AND gate (pObj)
        pFanin0 = Abc_NodeAigToSeq( pObj, 0, &nLatches0, &Init0 );
        pFanin1 = Abc_NodeAigToSeq( pObj, 1, &nLatches1, &Init1 );
        Abc_ObjAddFanin( pObj->pCopy, Abc_ObjGetCopy(pFanin0) );
        Abc_ObjAddFanin( pObj->pCopy, Abc_ObjGetCopy(pFanin1) );
        Abc_ObjAddFaninL0( pObj->pCopy, nLatches0 );
        Abc_ObjAddFaninL1( pObj->pCopy, nLatches1 );
        // add the initial state
        Vec_IntWriteEntry( pNtkNew->vInits, pObj->pCopy->Id, (Init1 << 16) | Init0 );
    }
    // reconnect the POs
    Abc_NtkForEachPo( pNtk, pObj, i )
    {
        // process the fanins
        pFanin0 = Abc_NodeAigToSeq( pObj, 0, &nLatches0, &Init0 );
        Abc_ObjAddFanin( pObj->pCopy, Abc_ObjGetCopy(pFanin0) );
        Abc_ObjAddFaninL0( pObj->pCopy, nLatches0 );
        // add the initial state
        Vec_IntWriteEntry( pNtkNew->vInits, pObj->pCopy->Id, Init0 );
    }
    // set the cutset composed of latch drivers
    pNtkNew->vLats = Abc_NtkAigCutsetCopy( pNtk );
    // copy EXDC and check correctness
    if ( pNtkNew->pExdc )
        fprintf( stdout, "Warning: EXDC is dropped when converting to sequential AIG.\n" );
    if ( !Abc_NtkCheck( pNtkNew ) )
        fprintf( stdout, "Abc_NtkAigToSeq(): Network check has failed.\n" );
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Collects the cut set nodes.]

  Description [These are internal AND gates that fanins into latches.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkAigCutsetCopy( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pLatch, * pDriver;
    int i;
    vNodes = Vec_PtrAlloc( Abc_NtkLatchNum(pNtk) );
    Abc_NtkIncrementTravId(pNtk);
    Abc_NtkForEachLatch( pNtk, pLatch, i )
    {
        pDriver = Abc_ObjFanin0(pLatch);
        if ( Abc_NodeIsTravIdCurrent(pDriver) || !Abc_NodeIsAigAnd(pDriver) )
            continue;
        Abc_NodeSetTravIdCurrent(pDriver);
        Vec_PtrPush( vNodes, pDriver->pCopy );
    }
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Determines the fanin that is transparent for latches.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NodeAigToSeq( Abc_Obj_t * pObj, int Num, int * pnLatches, int * pnInit )
{
    Abc_Obj_t * pFanin;
    int Init;
    // get the given fanin of the node
    pFanin = Abc_ObjFanin( pObj, Num );
    if ( !Abc_ObjIsLatch(pFanin) )
    {
        *pnLatches = *pnInit = 0;
        return Abc_ObjChild( pObj, Num );
    }
    pFanin = Abc_NodeAigToSeq( pFanin, 0, pnLatches, pnInit );
    // get the new initial state
    Init = Abc_LatchInit(pObj);
    assert( Init >= 0 && Init <= 3 );
    // complement the initial state if the inv is retimed over the latch
    if ( Abc_ObjIsComplement(pFanin) && Init < 2 ) // not a don't-care
        Init ^= 3;
    // update the latch number and initial state
    (*pnLatches)++;
    (*pnInit) = ((*pnInit) << 2) | Init;
    return Abc_ObjNotCond( pFanin, Abc_ObjFaninC(pObj,Num) );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


