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

/**Function*************************************************************

  Synopsis    [Counts the number of latches in the sequential AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ObjLatchGetInitNums( Abc_Obj_t * pObj, int Edge, int * pInits )
{
    Abc_InitType_t Init;
    int nLatches, i;
    nLatches = Abc_ObjFaninL( pObj, Edge );
    assert( nLatches <= ABC_MAX_EDGE_LATCH );
    for ( i = 0; i < nLatches; i++ )
    {
        Init = Abc_ObjFaninLGetInitOne( pObj, Edge, i );
        pInits[Init]++;
    }
}

/**Function*************************************************************

  Synopsis    [Counts the number of latches in the sequential AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkSeqLatchGetInitNums( Abc_Ntk_t * pNtk, int * pInits )
{
    Abc_Obj_t * pObj;
    int i;
    assert( Abc_NtkIsSeq( pNtk ) );
    for ( i = 0; i < 4; i++ )    
        pInits[i] = 0;
    Abc_NtkForEachPo( pNtk, pObj, i )
        Abc_ObjLatchGetInitNums( pObj, 0, pInits );
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        if ( Abc_ObjFaninNum(pObj) > 0 )
            Abc_ObjLatchGetInitNums( pObj, 0, pInits );
        if ( Abc_ObjFaninNum(pObj) > 1 )
            Abc_ObjLatchGetInitNums( pObj, 1, pInits );
    }
}

/**Function*************************************************************

  Synopsis    [Generates the printable edge label with the initial state.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_ObjFaninGetInitPrintable( Abc_Obj_t * pObj, int Edge )
{
    static char Buffer[ABC_MAX_EDGE_LATCH + 1];
    Abc_InitType_t Init;
    int nLatches, i;

    nLatches = Abc_ObjFaninL( pObj, Edge );
    assert( nLatches <= ABC_MAX_EDGE_LATCH );
    for ( i = 0; i < nLatches; i++ )
    {
        Init = Abc_ObjFaninLGetInitOne( pObj, Edge, i );
        if ( Init == ABC_INIT_NONE )
            Buffer[i] = '_';
        else if ( Init == ABC_INIT_ZERO )
            Buffer[i] = '0';
        else if ( Init == ABC_INIT_ONE )
            Buffer[i] = '1';
        else if ( Init == ABC_INIT_DC )
            Buffer[i] = 'x';
        else assert( 0 );
    }
    Buffer[nLatches] = 0;
    return Buffer;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


