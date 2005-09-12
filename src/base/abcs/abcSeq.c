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

#include "abcs.h"

/*
    A sequential network is similar to AIG in that it contains only
    AND gates. However, the AND-gates are currently not hashed. 

    When converting AIG into sequential AIG:
    - Const1/PIs/POs remain the same as in the original AIG.
    - Instead of the latches, a new cutset is added, which is currently
      defined as a set of AND gates that have a latch among their fanouts.
    - The edges of a sequential AIG are labeled with latch attributes
      in addition to the complementation attibutes. 
    - The attributes contain information about the number of latches 
       and their initial states. 
    - The number of latches is stored directly on the edges. The initial 
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
static Abc_Obj_t * Abc_NodeAigToSeq( Abc_Obj_t * pAnd, int Num, int * pnLatches, unsigned * pnInit );
static Abc_Obj_t * Abc_NodeSeqToLogic( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pFanin, int nLatches, unsigned Init );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Converts combinational AIG with latches into sequential AIG.]

  Description [The const/PI/PO nodes are duplicated. The internal
  nodes are duplicated in the topological order. The dangling nodes
  are not duplicated. The choice nodes are duplicated.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkAigToSeq( Abc_Ntk_t * pNtk )
{
    Abc_Ntk_t * pNtkNew;
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pObj, * pFanin;
    int i, Init, nLatches;
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
    {
        Abc_NtkDupObj(pNtkNew, pObj);
        pObj->pCopy->fPhase = pObj->fPhase; // needed for choices
    }
    // relink the choice nodes
    Vec_PtrForEachEntry( vNodes, pObj, i )
        if ( pObj->pData )
            pObj->pCopy->pData = ((Abc_Obj_t *)pObj->pData)->pCopy;
    Vec_PtrFree( vNodes );
    // start the storage for initial states
    pNtkNew->vInits = Vec_IntStart( 2 * Abc_NtkObjNumMax(pNtkNew) );
    // reconnect the internal nodes
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        // skip the constant and the PIs
        if ( Abc_ObjFaninNum(pObj) == 0 )
            continue;
        // process the first fanin
        pFanin = Abc_NodeAigToSeq( pObj, 0, &nLatches, &Init );
        Abc_ObjAddFanin( pObj->pCopy, Abc_ObjGetCopy(pFanin) );
        Abc_ObjAddFaninL0( pObj->pCopy, nLatches );
        Vec_IntWriteEntry( pNtkNew->vInits, 2 * i + 0, Init );
        if ( Abc_ObjFaninNum(pObj) == 1 )
            continue;
        // process the second fanin
        pFanin = Abc_NodeAigToSeq( pObj, 1, &nLatches, &Init );
        Abc_ObjAddFanin( pObj->pCopy, Abc_ObjGetCopy(pFanin) );
        Abc_ObjAddFaninL1( pObj->pCopy, nLatches );
        Vec_IntWriteEntry( pNtkNew->vInits, 2 * i + 1, Init );
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
Abc_Obj_t * Abc_NodeAigToSeq( Abc_Obj_t * pObj, int Num, int * pnLatches, unsigned * pnInit )
{
    Abc_Obj_t * pFanin;
    Abc_InitType_t Init;
    // get the given fanin of the node
    pFanin = Abc_ObjFanin( pObj, Num );
    if ( !Abc_ObjIsLatch(pFanin) )
    {
        *pnLatches = 0;
        *pnInit = 0;
        return Abc_ObjChild( pObj, Num );
    }
    pFanin = Abc_NodeAigToSeq( pFanin, 0, pnLatches, pnInit );
    // get the new initial state
    Init = Abc_LatchInit(pObj);
    // complement the initial state if the inv is retimed over the latch
    if ( Abc_ObjIsComplement(pFanin) ) 
    {
        if ( Init == ABC_INIT_ZERO )
            Init = ABC_INIT_ONE;
        else if ( Init == ABC_INIT_ONE )
            Init = ABC_INIT_ZERO;
        else if ( Init != ABC_INIT_DC )
            assert( 0 );
    }
    // update the latch number and initial state
    (*pnLatches)++;
    (*pnInit) = ((*pnInit) << 2) | Init;
    return Abc_ObjNotCond( pFanin, Abc_ObjFaninC(pObj,Num) );
}




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
    int i, nCutNodes, nDigits;
    unsigned Init;
    assert( Abc_NtkIsSeq(pNtk) );
    // start the network without latches
    nCutNodes = pNtk->vLats->nSize; pNtk->vLats->nSize = 0;
    pNtkNew = Abc_NtkStartFrom( pNtk, ABC_TYPE_LOGIC, ABC_FUNC_SOP );
    pNtk->vLats->nSize = nCutNodes;
    // create the constant node
    Abc_NtkDupConst1( pNtk, pNtkNew );
    // duplicate the nodes, create node functions
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        // skip the constant
        if ( Abc_ObjFaninNum(pObj) == 0 )
            continue;
        // duplicate the node
        Abc_NtkDupObj(pNtkNew, pObj);
        if ( Abc_ObjFaninNum(pObj) == 1 )
        {
            assert( !Abc_ObjFaninC0(pObj) );
            pObj->pCopy->pData = Abc_SopCreateBuf( pNtkNew->pManFunc );
            continue;
        }
        pObj->pCopy->pData = Abc_SopCreateAnd2( pNtkNew->pManFunc, Abc_ObjFaninC0(pObj), Abc_ObjFaninC1(pObj) );
    }
    // connect the objects
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        // skip PIs and the constant
        if ( Abc_ObjFaninNum(pObj) == 0 )
            continue;
        // get the initial states of the latches on the fanin edge of this node
        Init = Vec_IntEntry( pNtk->vInits, 2 * pObj->Id );
        // create the edge
        pFaninNew = Abc_NodeSeqToLogic( pNtkNew, Abc_ObjFanin0(pObj), Abc_ObjFaninL0(pObj), Init );
        Abc_ObjAddFanin( pObj->pCopy, pFaninNew );
        if ( Abc_ObjFaninNum(pObj) == 1 )
        {
            // create the complemented edge
            if ( Abc_ObjFaninC0(pObj) )
                Abc_ObjSetFaninC( pObj->pCopy, 0 );
            continue;
        }
        // get the initial states of the latches on the fanin edge of this node
        Init = Vec_IntEntry( pNtk->vInits, 2 * pObj->Id + 1 );
        // create the edge
        pFaninNew = Abc_NodeSeqToLogic( pNtkNew, Abc_ObjFanin1(pObj), Abc_ObjFaninL1(pObj), Init );
        Abc_ObjAddFanin( pObj->pCopy, pFaninNew );
        // the complemented edges are subsumed by the node function
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
        Abc_NtkLogicStoreName( pObjNew, Abc_ObjNameDummy("L", i, nDigits) );
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
Abc_Obj_t * Abc_NodeSeqToLogic( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pFanin, int nLatches, unsigned Init )
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


