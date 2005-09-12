/**CFile****************************************************************

  FileName    [abcUtils.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Utilities working sequential AIGs.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcUtils.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abcs.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Counts the number of latches in the sequential AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkSeqLatchNum( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    int i, Counter;
    assert( Abc_NtkIsSeq( pNtk ) );
    Counter = 0;
    Abc_NtkForEachNode( pNtk, pObj, i )
        Counter += Abc_ObjFaninLSum( pObj );
    Abc_NtkForEachPo( pNtk, pObj, i )
        Counter += Abc_ObjFaninLSum( pObj );
    return Counter;
}

/**Function*************************************************************

  Synopsis    [Counts the number of latches in the sequential AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkSeqLatchNumShared( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    int i, Counter;
    assert( Abc_NtkIsSeq( pNtk ) );
    Counter = 0;
    Abc_NtkForEachPi( pNtk, pObj, i )
        Counter += Abc_ObjFanoutLMax( pObj );
    Abc_NtkForEachNode( pNtk, pObj, i )
        Counter += Abc_ObjFanoutLMax( pObj );
    return Counter;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


