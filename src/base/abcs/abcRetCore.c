/**CFile****************************************************************

  FileName    [abcForBack.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Simple forward/backward retiming procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcForBack.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abcs.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

/* 
    Retiming can be represented in three equivalent forms:
    - as a set of integer lags for each node (array of chars by node ID)
    - as a set of node numbers with lag for each, fwd and bwd (two arrays of Abc_RetStep_t_)
    - as a set of node moves, fwd and bwd (two arrays arrays of Abc_Obj_t *)
*/

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs most forward retiming.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkSeqRetimeForward( Abc_Ntk_t * pNtk, int fVerbose )
{
    Vec_Ptr_t * vMoves;
    Abc_Obj_t * pNode;
    int i;
    // get the forward moves
    vMoves = Abc_NtkUtilRetimingTry( pNtk, 1 );
    // undo the forward moves
    Vec_PtrForEachEntryReverse( vMoves, pNode, i )
        Abc_ObjRetimeBackwardTry( pNode, 1 );
    // implement this forward retiming
    Abc_NtkImplementRetimingForward( pNtk, vMoves );
    Vec_PtrFree( vMoves ); 
}

/**Function*************************************************************

  Synopsis    [Performs most backward retiming.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkSeqRetimeBackward( Abc_Ntk_t * pNtk, int fVerbose )
{
    Vec_Ptr_t * vMoves;
    Abc_Obj_t * pNode;
    int i, RetValue;
    // get the backward moves
    vMoves = Abc_NtkUtilRetimingTry( pNtk, 0 );
    // undo the backward moves
    Vec_PtrForEachEntryReverse( vMoves, pNode, i )
        Abc_ObjRetimeForwardTry( pNode, 1 );
    // implement this backward retiming
    RetValue = Abc_NtkImplementRetimingBackward( pNtk, vMoves, fVerbose );
    Vec_PtrFree( vMoves ); 
    if ( RetValue == 0 )
        printf( "Retiming completed but initial state computation has failed.\n" );
}

/**Function*************************************************************

  Synopsis    [Performs performs optimal delay retiming.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkSeqRetimeDelay( Abc_Ntk_t * pNtk, int fVerbose )
{
    Vec_Str_t * vLags;
    int RetValue;
    // get the retiming vector
    vLags = Abc_NtkSeqRetimeDelayLags( pNtk, fVerbose );
    // implement this retiming
    RetValue = Abc_NtkImplementRetiming( pNtk, vLags, fVerbose );
    Vec_StrFree( vLags ); 
    if ( RetValue == 0 )
        printf( "Retiming completed but initial state computation has failed.\n" );
}

/**Function*************************************************************

  Synopsis    [Performs retiming for initial state computation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkSeqRetimeInitial( Abc_Ntk_t * pNtk, int fVerbose )
{
    Vec_Str_t * vLags;
    int RetValue;
    // get the retiming vector
    vLags = Abc_NtkSeqRetimeDelayLags( pNtk, fVerbose );
    // implement this retiming
    RetValue = Abc_NtkImplementRetiming( pNtk, vLags, fVerbose );
    Vec_StrFree( vLags ); 
    if ( RetValue == 0 )
        printf( "Retiming completed but initial state computation has failed.\n" );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


