/**CFile****************************************************************

  FileName    [ivyHaig.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    [HAIG management procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - May 11, 2006.]

  Revision    [$Id: ivyHaig.c,v 1.00 2006/05/11 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ivy.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

/* 
    HAIGing rules in working AIG:
    - The node points to the representative of its class
    - The pointer can be complemented if they have different polarity

    Choice node rules in HAIG:
    - Equivalent nodes are linked into a ring
    - Exactly one node in the ring has fanouts (this node is called representative)
    - Pointer going from a node to the next node in the ring is complemented 
      if the first node is complemented, compared to the representative node
    - The representative node always has non-complemented pointer to the next node
    - New nodes are inserted into the ring before the representative node
*/

// returns the representative node of the given HAIG node
static inline Ivy_Obj_t * Ivy_HaigObjRepr( Ivy_Obj_t * pObj )
{
    Ivy_Obj_t * pTemp;
    assert( !Ivy_IsComplement(pObj) );
    // if the node has no equivalent or has fanout, it is representative
    if ( pObj->pEquiv == NULL || Ivy_ObjRefs(pObj) > 0 )
        return pObj;
    // the node belongs to a class and is not a representative
    // complemented edge (pObj->pEquiv) tells if it is complemented w.r.t. the repr
    for ( pTemp = Ivy_Regular(pObj->pEquiv); pTemp != pObj; pTemp = Ivy_Regular(pTemp->pEquiv) )
        if ( Ivy_ObjRefs(pTemp) > 0 )
            break;
    // return the representative node
    assert( pTemp != pObj );
    return Ivy_NotCond( pTemp, Ivy_IsComplement(pObj->pEquiv) );
}

// counts the number of nodes in the equivalence class
static inline int Ivy_HaigObjCountClass( Ivy_Obj_t * pObj )
{
    Ivy_Obj_t * pTemp;
    int Counter;
    assert( !Ivy_IsComplement(pObj) );
    assert( Ivy_ObjRefs(pObj) > 0 );
    if ( pObj->pEquiv == NULL )
        return 1;
    Counter = 1;
    assert( !Ivy_IsComplement(pObj->pEquiv) );
    for ( pTemp = pObj->pEquiv; pTemp != pObj; pTemp = Ivy_Regular(pTemp->pEquiv) )
        Counter++;
    return Counter;
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts HAIG for the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManHaigStart( Ivy_Man_t * p )
{
    assert( p->pHaig == NULL );
    p->pHaig = Ivy_ManDup( p );
}

/**Function*************************************************************

  Synopsis    [Transfers the HAIG to the newly created manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManHaigTrasfer( Ivy_Man_t * p, Ivy_Man_t * pNew )
{
    Ivy_Obj_t * pObj;
    int i;
    assert( p->pHaig != NULL );
    Ivy_ManConst1(pNew)->pEquiv = Ivy_ManConst1(p)->pEquiv;
    Ivy_ManForEachPi( pNew, pObj, i )
        pObj->pEquiv = Ivy_ManPi( p, i )->pEquiv;
    pNew->pHaig = p->pHaig;
}

/**Function*************************************************************

  Synopsis    [Stops HAIG for the manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManHaigStop( Ivy_Man_t * p )
{
    Ivy_Obj_t * pObj;
    int i;
    assert( p->pHaig != NULL );
    Ivy_ManStop( p->pHaig );
    p->pHaig = NULL;
    // remove dangling pointers to the HAIG objects
    Ivy_ManForEachObj( p, pObj, i )
        pObj->pEquiv = NULL;
}

/**Function*************************************************************

  Synopsis    [Creates a new node in HAIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManHaigCreateObj( Ivy_Man_t * p, Ivy_Obj_t * pObj )
{
    assert( p->pHaig != NULL );
    assert( !Ivy_IsComplement(pObj) );
    if ( Ivy_ObjType(pObj) == IVY_BUF )
        pObj->pEquiv = Ivy_ObjChild0Equiv(pObj);
    else if ( Ivy_ObjType(pObj) == IVY_LATCH )
        pObj->pEquiv = Ivy_Latch( p->pHaig, Ivy_ObjChild0Equiv(pObj), pObj->Init );
    else if ( Ivy_ObjType(pObj) == IVY_AND )
        pObj->pEquiv = Ivy_And( p->pHaig, Ivy_ObjChild0Equiv(pObj), Ivy_ObjChild1Equiv(pObj) );
    else assert( 0 );
    // make sure the node points to the representative
    pObj->pEquiv = Ivy_NotCond( Ivy_HaigObjRepr(Ivy_Regular(pObj->pEquiv)), Ivy_IsComplement(pObj->pEquiv) );
}

/**Function*************************************************************

  Synopsis    [Sets the pair of equivalent nodes in HAIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManHaigCreateChoice( Ivy_Man_t * p, Ivy_Obj_t * pObjOld, Ivy_Obj_t * pObjNew )
{
    Ivy_Obj_t * pObjOldHaig, * pObjNewHaig;
    Ivy_Obj_t * pObjOldHaigR, * pObjNewHaigR;
    int fCompl;
    assert( p->pHaig != NULL );
    // get pointers to the classes
    pObjOldHaig = pObjOld->pEquiv;
    pObjNewHaig = Ivy_NotCond( Ivy_Regular(pObjNew)->pEquiv, Ivy_IsComplement(pObjNew) );
    // get regular pointers
    pObjOldHaigR = Ivy_Regular(pObjOldHaig);
    pObjNewHaigR = Ivy_Regular(pObjNewHaig);
    // check if there is phase difference between them
    fCompl = (Ivy_IsComplement(pObjOldHaig) != Ivy_IsComplement(pObjNewHaig));
    // if the class is the same, nothing to do
    if ( pObjOldHaigR == pObjNewHaigR )
        return;
    // combine classes
    // assume the second node does not belong to a class
    assert( pObjNewHaigR->pEquiv == NULL );
    // add this node to the class of pObjOldHaig
    if ( pObjOldHaigR->pEquiv == NULL )
        pObjNewHaigR->pEquiv = Ivy_NotCond( pObjOldHaigR, fCompl );
    else
        pObjNewHaigR->pEquiv = Ivy_NotCond( pObjOldHaigR->pEquiv, fCompl );
    pObjOldHaigR->pEquiv = pObjNewHaigR;
    // update the class of the new node
    Ivy_Regular(pObjNew)->pEquiv = Ivy_NotCond( pObjOldHaigR, fCompl ^ Ivy_IsComplement(pObjNew) );
}

/**Function*************************************************************

  Synopsis    [Count the number of choices and choice nodes in HAIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ivy_ManHaigCountChoices( Ivy_Man_t * p, int * pnChoices )
{
    Ivy_Obj_t * pObj;
    int nChoices, nChoiceNodes, Counter, i;
    assert( p->pHaig != NULL );
    nChoices = nChoiceNodes = 0;
    Ivy_ManForEachObj( p->pHaig, pObj, i )
    {
        if ( Ivy_ObjIsTerm(pObj) || i == 0 )
            continue;
        if ( Ivy_ObjRefs(pObj) == 0 )
        {
            assert( pObj->pEquiv == Ivy_HaigObjRepr(pObj) );
            continue;
        }
        Counter = Ivy_HaigObjCountClass( pObj );
        nChoiceNodes += (int)(Counter > 1);
        nChoices += Counter - 1;
    }
    *pnChoices = nChoices;
    return nChoiceNodes;
}

/**Function*************************************************************

  Synopsis    [Prints statistics of the HAIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManHaigPrintStats( Ivy_Man_t * p )
{
    int nChoices, nChoiceNodes;
    assert( p->pHaig != NULL );
    printf( "Original : " );
    Ivy_ManPrintStats( p );
    printf( "HAIG     : " );
    Ivy_ManPrintStats( p->pHaig );

    // print choice node stats
    nChoiceNodes = Ivy_ManHaigCountChoices( p, &nChoices );
    printf( "Total choice nodes = %d. Total choices = %d.\n", nChoiceNodes, nChoices ); 
    Ivy_ManHaigSimulate( p );
}


/**Function*************************************************************

  Synopsis    [Applies the simulation rules.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Ivy_Init_t Ivy_ManHaigSimulateAnd( Ivy_Init_t In0, Ivy_Init_t In1 )
{
    assert( In0 != IVY_INIT_NONE && In1 != IVY_INIT_NONE );
    if ( In0 == IVY_INIT_DC || In1 == IVY_INIT_DC )
        return IVY_INIT_DC;
    if ( In0 == IVY_INIT_1 && In1 == IVY_INIT_1 )
        return IVY_INIT_1;
    return IVY_INIT_0;
}

/**Function*************************************************************

  Synopsis    [Simulate HAIG using modified 3-valued simulation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ivy_ManHaigSimulate( Ivy_Man_t * p )
{
    Vec_Int_t * vNodes, * vLatches;
    Ivy_Obj_t * pObj;
    Ivy_Init_t In0, In1;
    int i, k, Counter;
    assert( p->pHaig != NULL );
    p = p->pHaig;
    // collect latches and nodes in the DFS order
    vNodes = Ivy_ManDfsSeq( p, &vLatches );
    // set the PI values
    Ivy_ManConst1(p)->Init = IVY_INIT_0;
    Ivy_ManForEachPi( p, pObj, i )
        pObj->Init = IVY_INIT_0;
    // set the latch values
    Ivy_ManForEachNodeVec( p, vLatches, pObj, i )
        pObj->Init = IVY_INIT_DC;
    // perform several rounds of simulation
    for ( k = 0; k < 5; k++ )
    {
        // count the number of non-determinate values
        Counter = 0;
        Ivy_ManForEachNodeVec( p, vLatches, pObj, i )
            Counter += ( pObj->Init == IVY_INIT_DC );
        printf( "Iter %d : Non-determinate = %d\n", k, Counter );               
        // simulate the internal nodes
        Ivy_ManForEachNodeVec( p, vNodes, pObj, i )
        {
            In0 = Ivy_InitNotCond( Ivy_ObjFanin0(pObj)->Init, Ivy_ObjFaninC0(pObj) );
            In1 = Ivy_InitNotCond( Ivy_ObjFanin1(pObj)->Init, Ivy_ObjFaninC1(pObj) );
            pObj->Init = Ivy_ManHaigSimulateAnd( In0, In1 );
        }
        // simulate the latches
        Ivy_ManForEachNodeVec( p, vLatches, pObj, i )
            pObj->Level = Ivy_ObjFanin0(pObj)->Init;
        Ivy_ManForEachNodeVec( p, vLatches, pObj, i )
            pObj->Init = pObj->Level, pObj->Level = 0;
    }
    // free arrays
    Vec_IntFree( vNodes );
    Vec_IntFree( vLatches );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


