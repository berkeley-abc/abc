/**CFile****************************************************************

  FileName    [ntkUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Various utilities.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntkUtil.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntk.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Increments the current traversal ID of the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_ManIncrementTravId( Ntk_Man_t * pNtk )
{
    Ntk_Obj_t * pObj;
    int i;
    if ( pNtk->nTravIds >= (1<<26)-1 )
    {
        pNtk->nTravIds = 0;
        Ntk_ManForEachObj( pNtk, pObj, i )
            pObj->TravId = 0;
    }
    pNtk->nTravIds++;
}

/**Function*************************************************************

  Synopsis    [Reads the maximum number of fanins.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntk_ManGetFaninMax( Ntk_Man_t * pNtk )
{
    Ntk_Obj_t * pNode;
    int i, nFaninsMax = 0;
    Ntk_ManForEachNode( pNtk, pNode, i )
    {
        if ( nFaninsMax < Ntk_ObjFaninNum(pNode) )
            nFaninsMax = Ntk_ObjFaninNum(pNode);
    }
    return nFaninsMax;
}

/**Function*************************************************************

  Synopsis    [Reads the total number of all fanins.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntk_ManGetTotalFanins( Ntk_Man_t * pNtk )
{
    Ntk_Obj_t * pNode;
    int i, nFanins = 0;
    Ntk_ManForEachNode( pNtk, pNode, i )
        nFanins += Ntk_ObjFaninNum(pNode);
    return nFanins;
}

/**Function*************************************************************

  Synopsis    [Computes the number of logic levels not counting PIs/POs.]

  Description [Assumes topological ordering of the nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntk_ManLevel( Ntk_Man_t * pNtk )
{
    Ntk_Obj_t * pObj, * pFanin;
    int i, k, LevelMax;
    Ntk_ManForEachPi( pNtk, pObj, i )
        Ntk_ObjSetLevel( pObj, 0 );
    Ntk_ManForEachNode( pNtk, pObj, i )
    {
        LevelMax = 0;
        Ntk_ObjForEachFanin( pObj, pFanin, k )
            if ( LevelMax < Ntk_ObjLevel(pFanin) )
                LevelMax = Ntk_ObjLevel(pFanin);
        Ntk_ObjSetLevel( pFanin, LevelMax+1 );
    }
    LevelMax = 0;
    Ntk_ManForEachPo( pNtk, pObj, i )
        if ( LevelMax < Ntk_ObjLevel(pObj) )
            LevelMax = Ntk_ObjLevel(pObj);
    return LevelMax;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntk_ManPiNum( Ntk_Man_t * pNtk )
{
    Ntk_Obj_t * pNode;
    int i, Counter = 0;
    Ntk_ManForEachPi( pNtk, pNode, i )
        Counter++;
    return Counter;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntk_ManPoNum( Ntk_Man_t * pNtk )
{
    Ntk_Obj_t * pNode;
    int i, Counter = 0;
    Ntk_ManForEachPo( pNtk, pNode, i )
        Counter++;
    return Counter;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


