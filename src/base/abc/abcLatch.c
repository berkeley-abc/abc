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


