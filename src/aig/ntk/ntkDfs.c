/**CFile****************************************************************

  FileName    [ntkDfs.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [DFS traversals.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntkDfs.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntk.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes the number of logic levels not counting PIs/POs.]

  Description [Assumes that white boxes have unit level.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntk_ManLevel( Ntk_Man_t * pNtk )
{
    Tim_Man_t * pManTimeUnit;
    Ntk_Obj_t * pObj, * pFanin;
    int i, k, LevelMax, Level;
    // clean the levels
    Ntk_ManForEachObj( pNtk, pObj, i )
        Ntk_ObjSetLevel( pObj, 0 );
    // perform level computation
    LevelMax = 0;
    pManTimeUnit = Tim_ManDupUnit( pNtk->pManTime );
    Tim_ManIncrementTravId( pManTimeUnit );
    Ntk_ManForEachObj( pNtk, pObj, i )
    {
        if ( Ntk_ObjIsCi(pObj) )
        {
            Level = (int)Tim_ManGetPiArrival( pManTimeUnit, pObj->PioId );
            Ntk_ObjSetLevel( pObj, Level );
        }
        else if ( Ntk_ObjIsCo(pObj) )
        {
            Level = Ntk_ObjLevel( Ntk_ObjFanin0(pObj) );
            Tim_ManSetPoArrival( pManTimeUnit, pObj->PioId, (float)Level );
            Ntk_ObjSetLevel( pObj, Level );
            if ( LevelMax < Ntk_ObjLevel(pObj) )
                LevelMax = Ntk_ObjLevel(pObj);
        }
        else if ( Ntk_ObjIsNode(pObj) )
        {
            Level = 0;
            Ntk_ObjForEachFanin( pObj, pFanin, k )
                if ( Level < Ntk_ObjLevel(pFanin) )
                    Level = Ntk_ObjLevel(pFanin);
            Ntk_ObjSetLevel( pObj, Level + 1 );
        }
        else
            assert( 0 );
    }
    // set the old timing manager
    Tim_ManStop( pManTimeUnit );
    return LevelMax;
}



/**Function*************************************************************

  Synopsis    [Performs DFS for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_ManLevel2_rec( Ntk_Obj_t * pObj )
{
    Ntk_Obj_t * pNext;
    int i, iBox, iTerm1, nTerms, LevelMax = 0;
    if ( Ntk_ObjIsTravIdCurrent( pObj ) )
        return;
    Ntk_ObjSetTravIdCurrent( pObj );
    if ( Ntk_ObjIsCi(pObj) )
    {
        iBox = Tim_ManBoxForCi( pObj->pMan->pManTime, pObj->PioId );
        if ( iBox >= 0 ) // this is not a true PI
        {
            iTerm1 = Tim_ManBoxInputFirst( pObj->pMan->pManTime, iBox );
            nTerms = Tim_ManBoxInputNum( pObj->pMan->pManTime, iBox );
            for ( i = 0; i < nTerms; i++ )
            {
                pNext = Ntk_ManCo(pObj->pMan, iTerm1 + i);
                Ntk_ManLevel2_rec( pNext );
                if ( LevelMax < Ntk_ObjLevel(pNext) )
                    LevelMax = Ntk_ObjLevel(pNext);
            }
            LevelMax++;
        }
    }
    else if ( Ntk_ObjIsNode(pObj) || Ntk_ObjIsCo(pObj) )
    {
        Ntk_ObjForEachFanin( pObj, pNext, i )
        {
            Ntk_ManLevel2_rec( pNext );
            if ( LevelMax < Ntk_ObjLevel(pNext) )
                LevelMax = Ntk_ObjLevel(pNext);
        }
        if ( Ntk_ObjIsNode(pObj) )
            LevelMax++;
    }
    else
        assert( 0 );
    Ntk_ObjSetLevel( pObj, LevelMax );
}

/**Function*************************************************************

  Synopsis    [Returns the DFS ordered array of all objects except latches.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntk_ManLevel2( Ntk_Man_t * pNtk )
{
    Ntk_Obj_t * pObj;
    int i, LevelMax = 0;
    Ntk_ManForEachObj( pNtk, pObj, i )
        Ntk_ObjSetLevel( pObj, 0 );
    Ntk_ManIncrementTravId( pNtk );
    Ntk_ManForEachPo( pNtk, pObj, i )
    {
        Ntk_ManLevel2_rec( pObj );
        if ( LevelMax < Ntk_ObjLevel(pObj) )
            LevelMax = Ntk_ObjLevel(pObj);
    }
    return LevelMax;
}



/**Function*************************************************************

  Synopsis    [Performs DFS for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_ManDfs_rec( Ntk_Obj_t * pObj, Vec_Ptr_t * vNodes )
{
    Ntk_Obj_t * pNext;
    int i;
    if ( Ntk_ObjIsTravIdCurrent( pObj ) )
        return;
    Ntk_ObjSetTravIdCurrent( pObj );
    Ntk_ObjForEachFanin( pObj, pNext, i )
        Ntk_ManDfs_rec( pNext, vNodes );
    Vec_PtrPush( vNodes, pObj );
}

/**Function*************************************************************

  Synopsis    [Returns the DFS ordered array of all objects except latches.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Ntk_ManDfs( Ntk_Man_t * pNtk )
{
    Vec_Ptr_t * vNodes;
    Ntk_Obj_t * pObj;
    int i;
    Ntk_ManIncrementTravId( pNtk );
    vNodes = Vec_PtrAlloc( 100 );
    Ntk_ManForEachObj( pNtk, pObj, i )
    {
        if ( Ntk_ObjIsCi(pObj) )
        {
            Ntk_ObjSetTravIdCurrent( pObj );
            Vec_PtrPush( vNodes, pObj );
        }
        else if ( Ntk_ObjIsCo(pObj) )
            Ntk_ManDfs_rec( pObj, vNodes );
    }
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Performs DFS for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntk_ManDfsReverse_rec( Ntk_Obj_t * pObj, Vec_Ptr_t * vNodes )
{
    Ntk_Obj_t * pNext;
    int i, iBox, iTerm1, nTerms;
    if ( Ntk_ObjIsTravIdCurrent( pObj ) )
        return;
    Ntk_ObjSetTravIdCurrent( pObj );
    if ( Ntk_ObjIsCo(pObj) )
    {
        iBox = Tim_ManBoxForCo( pObj->pMan->pManTime, pObj->PioId );
        if ( iBox >= 0 ) // this is not a true PO
        {
            iTerm1 = Tim_ManBoxOutputFirst( pObj->pMan->pManTime, iBox );
            nTerms = Tim_ManBoxOutputNum( pObj->pMan->pManTime, iBox );
            for ( i = 0; i < nTerms; i++ )
            {
                pNext = Ntk_ManCi(pObj->pMan, iTerm1 + i);
                Ntk_ManDfsReverse_rec( pNext, vNodes );
            }
        }
    }
    else if ( Ntk_ObjIsNode(pObj) || Ntk_ObjIsCi(pObj) )
    {
        Ntk_ObjForEachFanout( pObj, pNext, i )
            Ntk_ManDfsReverse_rec( pNext, vNodes );
    }
    else
        assert( 0 );
    Vec_PtrPush( vNodes, pObj );
}

/**Function*************************************************************

  Synopsis    [Returns the DFS ordered array of all objects except latches.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Ntk_ManDfsReverse( Ntk_Man_t * pNtk )
{
    Vec_Ptr_t * vNodes;
    Ntk_Obj_t * pObj;
    int i;
    Ntk_ManIncrementTravId( pNtk );
    vNodes = Vec_PtrAlloc( 100 );
    Ntk_ManForEachPi( pNtk, pObj, i )
        Ntk_ManDfsReverse_rec( pObj, vNodes );
    return vNodes;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


