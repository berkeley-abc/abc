/**CFile****************************************************************

  FileName    [dchChoice.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Choice computation for tech-mapping.]

  Synopsis    [Contrustion of choices.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 29, 2008.]

  Revision    [$Id: dchChoice.c,v 1.00 2008/07/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dchInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Counts the number of representatives.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dch_DeriveChoiceCountReprs( Aig_Man_t * pAig )
{
    Aig_Obj_t * pObj, * pRepr;
    int i, nReprs = 0;
    Aig_ManForEachObj( pAig, pObj, i )
    {
        pRepr = Aig_ObjRepr( pAig, pObj );
        if ( pRepr == NULL )
            continue;
        assert( pRepr->Id < pObj->Id );
        nReprs++;
    }
    return nReprs;
}

/**Function*************************************************************

  Synopsis    [Counts the number of equivalences.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dch_DeriveChoiceCountEquivs( Aig_Man_t * pAig )
{
    Aig_Obj_t * pObj, * pTemp, * pPrev;
    int i, nEquivs = 0, Counter = 0;
    Aig_ManForEachObj( pAig, pObj, i )
    {
        if ( !Aig_ObjIsChoice(pAig, pObj) )
            continue;
        for ( pPrev = pObj, pTemp = Aig_ObjEquiv(pAig, pObj); pTemp; 
              pPrev = pTemp, pTemp = Aig_ObjEquiv(pAig, pTemp) )
        {
            if ( pTemp->nRefs > 0 )
            {
                // remove referenced node from equivalence class
                assert( pAig->pEquivs[pPrev->Id] == pTemp );
                pAig->pEquivs[pPrev->Id] = pAig->pEquivs[pTemp->Id];
                pAig->pEquivs[pTemp->Id] = NULL;
                // how about the need to continue iterating over the list?
                // pPrev = pTemp ???
                Counter++;
            }
            nEquivs++;
        }
    }
//    printf( "Removed %d classes.\n", Counter );

    if ( Counter )
        Dch_DeriveChoiceCountEquivs( pAig );
//    if ( Counter )
//    printf( "Removed %d equiv nodes because of non-zero ref counter.\n", Counter );
    return nEquivs;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the choice node of pRepr is in the TFI of pObj.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dch_ObjCheckTfi_rec( Aig_Man_t * p, Aig_Obj_t * pObj )
{
    // check the trivial cases
    if ( pObj == NULL )
        return 0;
    if ( Aig_ObjIsPi(pObj) )
        return 0;
    if ( pObj->fMarkA )
        return 1;
    // skip the visited node
    if ( Aig_ObjIsTravIdCurrent( p, pObj ) )
        return 0;
    Aig_ObjSetTravIdCurrent( p, pObj );
    // check the children
    if ( Dch_ObjCheckTfi_rec( p, Aig_ObjFanin0(pObj) ) )
        return 1;
    if ( Dch_ObjCheckTfi_rec( p, Aig_ObjFanin1(pObj) ) )
        return 1;
    // check equivalent nodes
    return Dch_ObjCheckTfi_rec( p, Aig_ObjEquiv(p, pObj) );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the choice node of pRepr is in the TFI of pObj.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dch_ObjCheckTfi( Aig_Man_t * p, Aig_Obj_t * pObj, Aig_Obj_t * pRepr )
{
    Aig_Obj_t * pTemp;
    int RetValue;
    assert( !Aig_IsComplement(pObj) );
    assert( !Aig_IsComplement(pRepr) );
    // mark nodes of the choice node
    for ( pTemp = pRepr; pTemp; pTemp = Aig_ObjEquiv(p, pTemp) )
        pTemp->fMarkA = 1;
    // traverse the new node
    Aig_ManIncrementTravId( p );
    RetValue = Dch_ObjCheckTfi_rec( p, pObj );
    // unmark nodes of the choice node
    for ( pTemp = pRepr; pTemp; pTemp = Aig_ObjEquiv(p, pTemp) )
        pTemp->fMarkA = 0;
    return RetValue;
}

/**Function*************************************************************

  Synopsis    [Returns representatives of fanin in approapriate polarity.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Aig_Obj_t * Aig_ObjGetRepr( Aig_Man_t * p, Aig_Obj_t * pObj )
{
    Aig_Obj_t * pRepr;
    if ( (pRepr = Aig_ObjRepr(p, Aig_Regular(pObj))) )
        return Aig_NotCond( pRepr, Aig_Regular(pObj)->fPhase ^ pRepr->fPhase ^ Aig_IsComplement(pObj) );
    return pObj;
}

static inline Aig_Obj_t * Aig_ObjChild0CopyRepr( Aig_Man_t * p, Aig_Obj_t * pObj ) { return Aig_ObjGetRepr( p, Aig_ObjChild0Copy(pObj) ); }
static inline Aig_Obj_t * Aig_ObjChild1CopyRepr( Aig_Man_t * p, Aig_Obj_t * pObj ) { return Aig_ObjGetRepr( p, Aig_ObjChild1Copy(pObj) ); }

/**Function*************************************************************

  Synopsis    [Derives the AIG with choices from representatives.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dch_DeriveChoiceAigNode( Aig_Man_t * pAigNew, Aig_Man_t * pAigOld, Aig_Obj_t * pObj )
{
    Aig_Obj_t * pRepr, * pObjNew, * pReprNew;
    // get the new node
    pObj->pData = Aig_And( pAigNew, 
        Aig_ObjChild0CopyRepr(pAigNew, pObj), 
        Aig_ObjChild1CopyRepr(pAigNew, pObj) );
    pRepr = Aig_ObjRepr( pAigOld, pObj );
    if ( pRepr == NULL )
        return;
    // get the corresponding new nodes
    pObjNew  = Aig_Regular((Aig_Obj_t *)pObj->pData);
    pReprNew = Aig_Regular((Aig_Obj_t *)pRepr->pData);
    if ( pObjNew == pReprNew )
        return;
    // skip the earlier nodes
    if ( pReprNew->Id > pObjNew->Id )
        return;
    assert( pReprNew->Id < pObjNew->Id );
    // set the representatives
    Aig_ObjSetRepr( pAigNew, pObjNew, pReprNew );
    // skip used nodes
    if ( pObjNew->nRefs > 0 )
        return;
    assert( pObjNew->nRefs == 0 );
    // update new nodes of the object
    if ( !Aig_ObjIsNode(pRepr) )
        return;
    // skip choices with combinational loops
    if ( Dch_ObjCheckTfi( pAigNew, pObjNew, pReprNew ) )
        return;
    // add choice
    pAigNew->pEquivs[pObjNew->Id]  = pAigNew->pEquivs[pReprNew->Id];
    pAigNew->pEquivs[pReprNew->Id] = pObjNew;
}

/**Function*************************************************************

  Synopsis    [Derives the AIG with choices from representatives.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Dch_DeriveChoiceAig_old( Aig_Man_t * pAig )
{
    Aig_Man_t * pChoices, * pTemp;
    Aig_Obj_t * pObj;
    int i;
    // start recording equivalences
    pChoices = Aig_ManStart( Aig_ManObjNumMax(pAig) );
    pChoices->pEquivs = ABC_CALLOC( Aig_Obj_t *, Aig_ManObjNumMax(pAig) );
    pChoices->pReprs  = ABC_CALLOC( Aig_Obj_t *, Aig_ManObjNumMax(pAig) );
    // map constants and PIs
    Aig_ManCleanData( pAig );
    Aig_ManConst1(pAig)->pData = Aig_ManConst1(pChoices);
    Aig_ManForEachPi( pAig, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pChoices );
    // construct choices for the internal nodes
    assert( pAig->pReprs != NULL );
    Aig_ManForEachNode( pAig, pObj, i )
        Dch_DeriveChoiceAigNode( pChoices, pAig, pObj );
    Aig_ManForEachPo( pAig, pObj, i )
        Aig_ObjCreatePo( pChoices, Aig_ObjChild0CopyRepr(pChoices, pObj) );
    Dch_DeriveChoiceCountEquivs( pChoices );
    // there is no need for cleanup
    ABC_FREE( pChoices->pReprs );
    pChoices = Aig_ManDupDfs( pTemp = pChoices );
    Aig_ManStop( pTemp );
    return pChoices;
}




/**Function*************************************************************

  Synopsis    [Checks for combinational loops in the AIG.]

  Description [Returns 1 if combinational loop is detected.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManCheckAcyclic_rec( Aig_Man_t * p, Aig_Obj_t * pNode, int fVerbose )
{
    Aig_Obj_t * pFanin;
    int fAcyclic;
    if ( Aig_ObjIsPi(pNode) || Aig_ObjIsConst1(pNode) )
        return 1;
    assert( Aig_ObjIsNode(pNode) );
    // make sure the node is not visited
    assert( !Aig_ObjIsTravIdPrevious(p, pNode) );
    // check if the node is part of the combinational loop
    if ( Aig_ObjIsTravIdCurrent(p, pNode) )
    {
        if ( fVerbose )
            Abc_Print( 1, "Network \"%s\" contains combinational loop!\n", p->pSpec? p->pSpec : NULL );
        if ( fVerbose )
        Abc_Print( 1, "Node \"%d\" is encountered twice on the following path to the COs:\n", Aig_ObjId(pNode) );
        return 0;
    }
    // mark this node as a node on the current path
    Aig_ObjSetTravIdCurrent( p, pNode );

    // visit the transitive fanin
    pFanin = Aig_ObjFanin0(pNode);
    // check if the fanin is visited
    if ( !Aig_ObjIsTravIdPrevious(p, pFanin) ) 
    {
        // traverse the fanin's cone searching for the loop
        if ( !(fAcyclic = Aig_ManCheckAcyclic_rec(p, pFanin, fVerbose)) )
        {
            // return as soon as the loop is detected
            if ( fVerbose )
            Abc_Print( 1, " %d ->", Aig_ObjId(pFanin) );
            return 0;
        }
    }

    // visit the transitive fanin
    pFanin = Aig_ObjFanin1(pNode);
    // check if the fanin is visited
    if ( !Aig_ObjIsTravIdPrevious(p, pFanin) ) 
    {
        // traverse the fanin's cone searching for the loop
        if ( !(fAcyclic = Aig_ManCheckAcyclic_rec(p, pFanin, fVerbose)) )
        {
            // return as soon as the loop is detected
            if ( fVerbose )
            Abc_Print( 1, " %d ->", Aig_ObjId(pFanin) );
            return 0;
        }
    }

    // visit choices
    if ( Aig_ObjRepr(p, pNode) == NULL && Aig_ObjEquiv(p, pNode) != NULL )
    {
        for ( pFanin = Aig_ObjEquiv(p, pNode); pFanin; pFanin = Aig_ObjEquiv(p, pFanin) )
        {
            // check if the fanin is visited
            if ( Aig_ObjIsTravIdPrevious(p, pFanin) ) 
                continue;
            // traverse the fanin's cone searching for the loop
            if ( (fAcyclic = Aig_ManCheckAcyclic_rec(p, pFanin, fVerbose)) )
                continue;
            // return as soon as the loop is detected
            if ( fVerbose )
            Abc_Print( 1, " %d", Aig_ObjId(pFanin) );
            if ( fVerbose )
            Abc_Print( 1, " (choice of %d) -> ", Aig_ObjId(pNode) );
            return 0;
        }
    }
    // mark this node as a visited node
    Aig_ObjSetTravIdPrevious( p, pNode );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Checks for combinational loops in the AIG.]

  Description [Returns 1 if there is no combinational loops.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManCheckAcyclic( Aig_Man_t * p, int fVerbose )
{
    Aig_Obj_t * pNode;
    int fAcyclic;
    int i;
    // set the traversal ID for this DFS ordering
    Aig_ManIncrementTravId( p );   
    Aig_ManIncrementTravId( p );   
    // pNode->TravId == pNet->nTravIds      means "pNode is on the path"
    // pNode->TravId == pNet->nTravIds - 1  means "pNode is visited but is not on the path"
    // pNode->TravId <  pNet->nTravIds - 1  means "pNode is not visited"
    // traverse the network to detect cycles
    fAcyclic = 1;
    Aig_ManForEachPo( p, pNode, i )
    {
        pNode = Aig_ObjFanin0(pNode);
        if ( Aig_ObjIsTravIdPrevious(p, pNode) )
            continue;
        // traverse the output logic cone
        if ( (fAcyclic = Aig_ManCheckAcyclic_rec(p, pNode, fVerbose)) )
            continue;
        // stop as soon as the first loop is detected
        if ( fVerbose )
        Abc_Print( 1, " CO %d\n", i );
        break;
    }
    return fAcyclic;
}

/**Function*************************************************************

  Synopsis    [Removes combinational loop.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManFixLoopProblem( Aig_Man_t * p, int fVerbose )
{
    Aig_Obj_t * pObj;
    int i, Counter = 0, Counter2 = 0;
    Aig_ManForEachObj( p, pObj, i )
    {
        if ( !Aig_ObjIsTravIdCurrent(p, pObj) )
            continue;
        Counter2++;
        if ( Aig_ObjRepr(p, pObj) == NULL && Aig_ObjEquiv(p, pObj) != NULL )
        {
            Aig_ObjSetEquiv(p, pObj, NULL);
            Counter++;
        }
    }
    if ( fVerbose )
    Abc_Print( 1, "Fixed %d choice nodes on the path with %d objects.\n", Counter, Counter2 );
}


/**Function*************************************************************

  Synopsis    [Derives the AIG with choices from representatives.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Dch_DeriveChoiceAigInt( Aig_Man_t * pAig )
{
    Aig_Man_t * pChoices;
    Aig_Obj_t * pObj;
    int i;
    // start recording equivalences
    pChoices = Aig_ManStart( Aig_ManObjNumMax(pAig) );
    pChoices->pEquivs = ABC_CALLOC( Aig_Obj_t *, Aig_ManObjNumMax(pAig) );
    pChoices->pReprs  = ABC_CALLOC( Aig_Obj_t *, Aig_ManObjNumMax(pAig) );
    // map constants and PIs
    Aig_ManCleanData( pAig );
    Aig_ManConst1(pAig)->pData = Aig_ManConst1(pChoices);
    Aig_ManForEachPi( pAig, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pChoices );
    // construct choices for the internal nodes
    assert( pAig->pReprs != NULL );
    Aig_ManForEachNode( pAig, pObj, i )
        Dch_DeriveChoiceAigNode( pChoices, pAig, pObj );
    Aig_ManForEachPo( pAig, pObj, i )
        Aig_ObjCreatePo( pChoices, Aig_ObjChild0CopyRepr(pChoices, pObj) );
    Dch_DeriveChoiceCountEquivs( pChoices );
    Aig_ManSetRegNum( pChoices, Aig_ManRegNum(pAig) );
    return pChoices;
}

/**Function*************************************************************

  Synopsis    [Derives the AIG with choices from representatives.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Dch_DeriveChoiceAig( Aig_Man_t * pAig )
{
    extern int Aig_ManCheckAcyclic( Aig_Man_t * pAig, int fVerbose );
    Aig_Man_t * pChoices, * pTemp;
    int fVerbose = 0;
    pChoices = Dch_DeriveChoiceAigInt( pAig );
//    pChoices = Dch_DeriveChoiceAigInt( pTemp = pChoices );
//    Aig_ManStop( pTemp );
    // there is no need for cleanup
    ABC_FREE( pChoices->pReprs );
    while ( !Aig_ManCheckAcyclic( pChoices, fVerbose ) )
    {
        if ( fVerbose )
        Abc_Print( 1, "There is a loop!\n" );
        Aig_ManFixLoopProblem( pChoices, fVerbose );
    }
    pChoices = Aig_ManDupDfs( pTemp = pChoices );
    Aig_ManStop( pTemp );
    return pChoices;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

