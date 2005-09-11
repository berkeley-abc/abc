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

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the latch number of the fanout.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ObjFanoutL( Abc_Obj_t * pObj, Abc_Obj_t * pFanout )
{
    assert( Abc_NtkIsSeq(pObj->pNtk) );
    if ( Abc_ObjFaninId0(pFanout) == (int)pObj->Id )
        return Abc_ObjFaninL0(pFanout);
    else if ( Abc_ObjFaninId1(pFanout) == (int)pObj->Id )
        return Abc_ObjFaninL1(pFanout);
    else 
        assert( 0 );
    return 0;
}

/**Function*************************************************************

  Synopsis    [Sets the latch number of the fanout.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ObjSetFanoutL( Abc_Obj_t * pObj, Abc_Obj_t * pFanout, int nLats )  
{ 
    assert( Abc_NtkIsSeq(pObj->pNtk) );
    if ( Abc_ObjFaninId0(pFanout) == (int)pObj->Id )
        Abc_ObjSetFaninL0(pFanout, nLats);
    else if ( Abc_ObjFaninId1(pFanout) == (int)pObj->Id )
        Abc_ObjSetFaninL1(pFanout, nLats);
    else 
        assert( 0 );
}

/**Function*************************************************************

  Synopsis    [Adds to the latch number of the fanout.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ObjAddFanoutL( Abc_Obj_t * pObj, Abc_Obj_t * pFanout, int nLats )  
{ 
    assert( Abc_NtkIsSeq(pObj->pNtk) );
    if ( Abc_ObjFaninId0(pFanout) == (int)pObj->Id )
        Abc_ObjAddFaninL0(pFanout, nLats);
    else if ( Abc_ObjFaninId1(pFanout) == (int)pObj->Id )
        Abc_ObjAddFaninL1(pFanout, nLats);
    else 
        assert( 0 );
}

/**Function*************************************************************

  Synopsis    [Returns the latch number of the fanout.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ObjFanoutLMax( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    int i, nLatchCur, nLatchRes;
    nLatchRes = 0;
    Abc_ObjForEachFanout( pObj, pFanout, i )
    {
        nLatchCur = Abc_ObjFanoutL(pObj, pFanout);
        if ( nLatchRes < nLatchCur )
            nLatchRes = nLatchCur;
    }
    assert( nLatchRes >= 0 );
    return nLatchRes;
}

/**Function*************************************************************

  Synopsis    [Returns the latch number of the fanout.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ObjFanoutLMin( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    int i, nLatchCur, nLatchRes;
    nLatchRes = ABC_INFINITY;
    Abc_ObjForEachFanout( pObj, pFanout, i )
    {
        nLatchCur = Abc_ObjFanoutL(pObj, pFanout);
        if ( nLatchRes > nLatchCur )
            nLatchRes = nLatchCur;
    }
    assert( nLatchRes < ABC_INFINITY );
    return nLatchRes;
}

/**Function*************************************************************

  Synopsis    [Returns the sum of latches on the fanout edges.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ObjFanoutLSum( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanout;
    int i, nSum = 0;
    Abc_ObjForEachFanout( pObj, pFanout, i )
        nSum += Abc_ObjFanoutL(pObj, pFanout);
    return nSum;
}

/**Function*************************************************************

  Synopsis    [Returns the sum of latches on the fanin edges.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ObjFaninLSum( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanin;
    int i, nSum = 0;
    Abc_ObjForEachFanin( pObj, pFanin, i )
        nSum += Abc_ObjFaninL(pObj, i);
    return nSum;
}

/**Function*************************************************************

  Synopsis    [Counters the number of latches in the sequential AIG.]

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

  Synopsis    [Counters the number of latches in the sequential AIG.]

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


