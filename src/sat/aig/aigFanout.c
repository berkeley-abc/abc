/**CFile****************************************************************

  FileName    [aigFanout.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: aigFanout.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline Aig_Node_t *  Aig_NodeFanPivot( Aig_Node_t * pNode )                { return Vec_PtrEntry(pNode->pMan->vFanPivots, pNode->Id); }
static inline Aig_Node_t *  Aig_NodeFanFan0( Aig_Node_t * pNode )                 { return Vec_PtrEntry(pNode->pMan->vFanFans0, pNode->Id);  }
static inline Aig_Node_t *  Aig_NodeFanFan1( Aig_Node_t * pNode )                 { return Vec_PtrEntry(pNode->pMan->vFanFans1, pNode->Id);  }
static inline Aig_Node_t ** Aig_NodeFanPivotPlace( Aig_Node_t * pNode )           { return ((Aig_Node_t **)pNode->pMan->vFanPivots->pArray) + pNode->Id; }
static inline Aig_Node_t ** Aig_NodeFanFan0Place( Aig_Node_t * pNode )            { return ((Aig_Node_t **)pNode->pMan->vFanFans0->pArray) + pNode->Id;  }
static inline Aig_Node_t ** Aig_NodeFanFan1Place( Aig_Node_t * pNode )            { return ((Aig_Node_t **)pNode->pMan->vFanFans1->pArray) + pNode->Id;  }
static inline void Aig_NodeSetFanPivot( Aig_Node_t * pNode, Aig_Node_t * pNode2 ) { Vec_PtrWriteEntry(pNode->pMan->vFanPivots, pNode->Id, pNode2); }
static inline void Aig_NodeSetFanFan0( Aig_Node_t * pNode, Aig_Node_t * pNode2 )  { Vec_PtrWriteEntry(pNode->pMan->vFanFans0, pNode->Id, pNode2);  }
static inline void Aig_NodeSetFanFan1( Aig_Node_t * pNode, Aig_Node_t * pNode2 )  { Vec_PtrWriteEntry(pNode->pMan->vFanFans1, pNode->Id, pNode2);  }
static inline Aig_Node_t * Aig_NodeNextFanout( Aig_Node_t * pNode, Aig_Node_t * pFanout )       { if ( pFanout == NULL ) return NULL; return Aig_NodeFaninId0(pFanout) == pNode->Id? Aig_NodeFanFan0(pFanout) : Aig_NodeFanFan1(pFanout); }
static inline Aig_Node_t ** Aig_NodeNextFanoutPlace( Aig_Node_t * pNode, Aig_Node_t * pFanout ) { return Aig_NodeFaninId0(pFanout) == pNode->Id? Aig_NodeFanFan0Place(pFanout) : Aig_NodeFanFan1Place(pFanout); }

// iterator through the fanouts of the node
#define Aig_NodeForEachFanout( pNode, pFanout )                           \
    for ( pFanout = Aig_NodeFanPivot(pNode); pFanout;                     \
          pFanout = Aig_NodeNextFanout(pNode, pFanout) )
// safe iterator through the fanouts of the node
#define Aig_NodeForEachFanoutSafe( pNode, pFanout, pFanout2 )             \
    for ( pFanout  = Aig_NodeFanPivot(pNode),                             \
          pFanout2 = Aig_NodeNextFanout(pNode, pFanout);              \
          pFanout;                                                        \
          pFanout  = pFanout2,                                            \
          pFanout2 = Aig_NodeNextFanout(pNode, pFanout) )

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates the fanouts for all nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManCreateFanouts( Aig_Man_t * p )
{
    Aig_Node_t * pNode;
    int i;
    assert( p->vFanPivots == NULL );
    p->vFanPivots = Vec_PtrStart( Aig_ManNodeNum(p) );
    p->vFanFans0  = Vec_PtrStart( Aig_ManNodeNum(p) );
    p->vFanFans1  = Vec_PtrStart( Aig_ManNodeNum(p) );
    Aig_ManForEachNode( p, pNode, i )
    {
        if ( Aig_NodeIsPi(pNode) || i == 0 )
            continue;
        Aig_NodeAddFaninFanout( Aig_NodeFanin0(pNode), pNode );
        if ( Aig_NodeIsPo(pNode) )
            continue;
        Aig_NodeAddFaninFanout( Aig_NodeFanin1(pNode), pNode );
    }
}

/**Function*************************************************************

  Synopsis    [Creates the fanouts for all nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Aig_ManResizeFanouts( Aig_Man_t * p, int nSizeNew )
{
    assert( p->vFanPivots );
    if ( Vec_PtrSize(p->vFanPivots) < nSizeNew )
    {
        Vec_PtrFillExtra( p->vFanPivots, nSizeNew + 1000, NULL );
        Vec_PtrFillExtra( p->vFanFans0,  nSizeNew + 1000, NULL );
        Vec_PtrFillExtra( p->vFanFans1,  nSizeNew + 1000, NULL );
    }
}

/**Function*************************************************************

  Synopsis    [Add the fanout to the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_NodeAddFaninFanout( Aig_Node_t * pFanin, Aig_Node_t * pFanout )
{
    Aig_Node_t * pPivot;

    // check that they are not complemented
    assert( !Aig_IsComplement(pFanin) );
    assert( !Aig_IsComplement(pFanout) );
    // check that pFanins is a fanin of pFanout
    assert( Aig_NodeFaninId0(pFanout) == pFanin->Id || Aig_NodeFaninId1(pFanout) == pFanin->Id );

    // resize the fanout manager
    Aig_ManResizeFanouts( pFanin->pMan, 1 + AIG_MAX(pFanin->Id, pFanout->Id) );

    // consider the case of the first fanout
    pPivot = Aig_NodeFanPivot(pFanin);
    if ( pPivot == NULL )
    {
        Aig_NodeSetFanPivot( pFanin, pFanout );
        return;
    }

    // consider the case of more than one fanouts
    if ( Aig_NodeFaninId0(pPivot) == pFanin->Id )
    {
        if ( Aig_NodeFaninId0(pFanout) == pFanin->Id )
        {
            Aig_NodeSetFanFan0( pFanout, Aig_NodeFanFan0(pPivot) );
            Aig_NodeSetFanFan0( pPivot, pFanout );
        }
        else // if ( Aig_NodeFaninId1(pFanout) == pFanin->Id )
        {
            Aig_NodeSetFanFan1( pFanout, Aig_NodeFanFan0(pPivot) );
            Aig_NodeSetFanFan0( pPivot, pFanout );
        }
    }
    else // if ( Aig_NodeFaninId1(pPivot) == pFanin->Id )
    {
        assert( Aig_NodeFaninId1(pPivot) == pFanin->Id );
        if ( Aig_NodeFaninId0(pFanout) == pFanin->Id )
        {
            Aig_NodeSetFanFan0( pFanout, Aig_NodeFanFan1(pPivot) );
            Aig_NodeSetFanFan1( pPivot, pFanout );
        }
        else // if ( Aig_NodeFaninId1(pFanout) == pFanin->Id )
        {
            Aig_NodeSetFanFan1( pFanout, Aig_NodeFanFan1(pPivot) );
            Aig_NodeSetFanFan1( pPivot, pFanout );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Add the fanout to the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_NodeRemoveFaninFanout( Aig_Node_t * pFanin, Aig_Node_t * pFanoutToRemove )
{
    Aig_Node_t * pFanout, * pFanout2, ** ppFanList;
    // start the linked list of fanouts
    ppFanList = Aig_NodeFanPivotPlace(pFanin); 
    // go through the fanouts
    Aig_NodeForEachFanoutSafe( pFanin, pFanout, pFanout2 )
    {
        // skip the fanout-to-remove
        if ( pFanout == pFanoutToRemove )
            continue;
        // add useful fanouts to the list
        *ppFanList = pFanout;
        ppFanList = Aig_NodeNextFanoutPlace( pFanin, pFanout );
    }
    *ppFanList = NULL;
}

/**Function*************************************************************

  Synopsis    [Returns the number of fanouts of a node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_NodeGetFanoutNum( Aig_Node_t * pNode )
{
    Aig_Node_t * pFanout;
    int Counter = 0;
    Aig_NodeForEachFanout( pNode, pFanout )
        Counter++;
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Collect fanouts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Aig_NodeGetFanouts( Aig_Node_t * pNode )
{
    Aig_Node_t * pFanout;
    Vec_PtrClear( pNode->pMan->vFanouts );
    Aig_NodeForEachFanout( pNode, pFanout )
        Vec_PtrPush( pNode->pMan->vFanouts, pFanout );
    return pNode->pMan->vFanouts;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the node has at least one complemented fanout.]

  Description [A fanout is complemented if the fanout's fanin edge pointing
  to the given node is complemented.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Aig_NodeHasComplFanoutEdge( Aig_Node_t * pNode )
{
    Aig_Node_t * pFanout;
    int iFanin;
    Aig_NodeForEachFanout( pNode, pFanout )
    {
        iFanin = Aig_NodeWhatFanin( pFanout, pNode );
        assert( iFanin >= 0 );
        if ( iFanin && Aig_NodeFaninC1(pFanout) || !iFanin && Aig_NodeFaninC0(pFanout) )
            return 1;
    }
    return 0;
}




/**Function*************************************************************

  Synopsis    [Recursively computes and assigns the reverse level of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Aig_NodeSetLevelR_rec( Aig_Node_t * pNode )
{
    Aig_Node_t * pFanout;
    int LevelR = 0;
    if ( Aig_NodeIsPo(pNode) )
        return pNode->LevelR = 0;
    Aig_NodeForEachFanout( pNode, pFanout )
        if ( LevelR < Aig_NodeSetLevelR_rec(pFanout) )
            LevelR = pFanout->LevelR;
    return pNode->LevelR = 1 + LevelR;
}

/**Function*************************************************************

  Synopsis    [Computes the reverse level of all nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManSetLevelR( Aig_Man_t * pMan )
{
    Aig_Node_t * pNode;
    int i, LevelR = 0;
    Aig_ManForEachPi( pMan, pNode, i )
        if ( LevelR < Aig_NodeSetLevelR_rec(pNode) )
            LevelR = pNode->LevelR;
    return LevelR;
}

/**Function*************************************************************

  Synopsis    [Computes the global number of logic levels.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManGetLevelMax( Aig_Man_t * pMan )
{
    Aig_Node_t * pNode;
    int i, LevelsMax = 0;
    Aig_ManForEachPo( pMan, pNode, i )
        if ( LevelsMax < (int)pNode->Level )
            LevelsMax = (int)pNode->Level;
    return LevelsMax;
}

/**Function*************************************************************

  Synopsis    [Computes but does not assign the reverse level of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_NodeGetLevelRNew( Aig_Node_t * pNode )
{
    Aig_Node_t * pFanout;
    unsigned LevelR = 0;
    Aig_NodeForEachFanout( pNode, pFanout )
        LevelR = AIG_MAX( LevelR, pFanout->LevelR );
    return LevelR + !Aig_NodeIsPi(pNode);
}


/**Function*************************************************************

  Synopsis    [Updates the direct level of one node.]

  Description [Returns 1 if direct level of at least one CO was changed.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_NodeUpdateLevel_int( Aig_Node_t * pNode )
{
    Aig_Node_t * pFanout;
    unsigned LevelNew, fStatus = 0;
    Aig_NodeForEachFanout( pNode, pFanout )
    {
        LevelNew = Aig_NodeGetLevelNew( pFanout );
        if ( pFanout->Level == LevelNew )
            continue;
        // the level has changed
        pFanout->Level = LevelNew;
        if ( Aig_NodeIsPo(pNode) )
            fStatus = 1;
        else
            fStatus |= Aig_NodeUpdateLevel_int( pFanout );
    }
    return fStatus;    
}


/**Function*************************************************************

  Synopsis    [Updates the reverse level of one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_NodeUpdateLevelR_int( Aig_Node_t * pNode )
{
    Aig_Node_t * pFanin;
    unsigned LevelNew;
    assert( !Aig_NodeIsPo(pNode) );
    pFanin = Aig_NodeFanin0(pNode);
    LevelNew = Aig_NodeGetLevelRNew(pFanin);
    if ( pFanin->LevelR != LevelNew )
    {
        pFanin->LevelR = LevelNew;
        if ( Aig_NodeIsAnd(pFanin) )
            Aig_NodeUpdateLevelR_int( pFanin );
    }
    pFanin = Aig_NodeFanin1(pNode);
    LevelNew = Aig_NodeGetLevelRNew(pFanin);
    if ( pFanin->LevelR != LevelNew )
    {
        pFanin->LevelR = LevelNew;
        if ( Aig_NodeIsAnd(pFanin) )
            Aig_NodeUpdateLevelR_int( pFanin );
    }
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


