/**CFile****************************************************************

  FileName    [abcRetUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Retiming utilities.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcRetUtil.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abcs.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs forward retiming of the sequential AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkUtilRetimingTry( Abc_Ntk_t * pNtk, bool fForward )
{
    Vec_Ptr_t * vNodes, * vMoves;
    Abc_Obj_t * pNode, * pFanout, * pFanin;
    int i, k, nLatches;
    assert( Abc_NtkIsSeq( pNtk ) );
    // assume that all nodes can be retimed
    vNodes = Vec_PtrAlloc( 100 );
    Abc_AigForEachAnd( pNtk, pNode, i )
    {
        Vec_PtrPush( vNodes, pNode );
        pNode->fMarkA = 1;
    }
    // process the nodes
    vMoves = Vec_PtrAlloc( 100 );
    Vec_PtrForEachEntry( vNodes, pNode, i )
    {
//        printf( "(%d,%d) ", Abc_ObjFaninL0(pNode), Abc_ObjFaninL0(pNode) );
        // unmark the node as processed
        pNode->fMarkA = 0;
        // get the number of latches to retime
        if ( fForward )
            nLatches = Abc_ObjFaninLMin(pNode);
        else
            nLatches = Abc_ObjFanoutLMin(pNode);
        if ( nLatches == 0 )
            continue;
        assert( nLatches > 0 );
        // retime the latches forward
        if ( fForward )
            Abc_ObjRetimeForwardTry( pNode, nLatches );
        else
            Abc_ObjRetimeBackwardTry( pNode, nLatches );
        // write the moves
        for ( k = 0; k < nLatches; k++ )
            Vec_PtrPush( vMoves, pNode );
        // schedule fanouts for updating
        if ( fForward )
        {
            Abc_ObjForEachFanout( pNode, pFanout, k )
            {
                if ( Abc_ObjFaninNum(pFanout) != 2 || pFanout->fMarkA )
                    continue;
                pFanout->fMarkA = 1;
                Vec_PtrPush( vNodes, pFanout );
            }
        }
        else
        {
            Abc_ObjForEachFanin( pNode, pFanin, k )
            {
                if ( Abc_ObjFaninNum(pFanin) != 2 || pFanin->fMarkA )
                    continue;
                pFanin->fMarkA = 1;
                Vec_PtrPush( vNodes, pFanin );
            }
        }
    }
    Vec_PtrFree( vNodes );
    // make sure the marks are clean the the retiming is final
    Abc_AigForEachAnd( pNtk, pNode, i )
    {
        assert( pNode->fMarkA == 0 );
        if ( fForward ) 
            assert( Abc_ObjFaninLMin(pNode) == 0 );
        else
            assert( Abc_ObjFanoutLMin(pNode) == 0 );
    }
    return vMoves;
}

/**Function*************************************************************

  Synopsis    [Translates retiming steps into retiming moves.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkUtilRetimingGetMoves( Abc_Ntk_t * pNtk, Vec_Int_t * vSteps, bool fForward )
{
    Abc_RetStep_t RetStep;
    Vec_Ptr_t * vMoves;
    Abc_Obj_t * pNode;
    int i, k, iNode, nLatches, Number;
    int fChange;
    assert( Abc_NtkIsSeq( pNtk ) );
    // process the nodes
    vMoves = Vec_PtrAlloc( 100 );
    while ( Vec_IntSize(vSteps) > 0 )
    {
        iNode = 0;
        fChange = 0;
        Vec_IntForEachEntry( vSteps, Number, i )
        {
            // get the retiming step
            RetStep = Abc_Int2RetStep( Number );
            // get the node to be retimed
            pNode = Abc_NtkObj( pNtk, RetStep.iNode );
            assert( RetStep.nLatches > 0 );
            // get the number of latches that can be retimed
            if ( fForward )
                nLatches = Abc_ObjFaninLMin(pNode);
            else
                nLatches = Abc_ObjFanoutLMin(pNode);
            if ( nLatches == 0 )
            {
                Vec_IntWriteEntry( vSteps, iNode++, Abc_RetStep2Int(RetStep) );
                continue;
            }
            assert( nLatches > 0 );
            fChange = 1;
            // get the number of latches to be retimed over this node
            nLatches = ABC_MIN( nLatches, (int)RetStep.nLatches );
            // retime the latches forward
            if ( fForward )
                Abc_ObjRetimeForwardTry( pNode, nLatches );
            else
                Abc_ObjRetimeBackwardTry( pNode, nLatches );
            // write the moves
            for ( k = 0; k < nLatches; k++ )
                Vec_PtrPush( vMoves, pNode );
            // subtract the retiming performed
            RetStep.nLatches -= nLatches;
            // store the node if it is not retimed completely
            if ( RetStep.nLatches > 0 )
                Vec_IntWriteEntry( vSteps, iNode++, Abc_RetStep2Int(RetStep) );
        }
        // reduce the array
        Vec_IntShrink( vSteps, iNode );
        if ( !fChange )
        {
            printf( "Warning: %d strange steps.\n", Vec_IntSize(vSteps) );
            /*
            Vec_IntForEachEntry( vSteps, Number, i )
            {
                RetStep = Abc_Int2RetStep( Number );
                printf( "%d(%d) ", RetStep.iNode, RetStep.nLatches );
            }
            printf( "\n" );
            */
            break;
        }
    }
    // undo the tentative retiming
    if ( fForward )
    {
        Vec_PtrForEachEntryReverse( vMoves, pNode, i )
            Abc_ObjRetimeBackwardTry( pNode, 1 );
    }
    else
    {
        Vec_PtrForEachEntryReverse( vMoves, pNode, i )
            Abc_ObjRetimeForwardTry( pNode, 1 );
    }
    return vMoves;
}


/**Function*************************************************************

  Synopsis    [Splits retiming into forward and backward.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_NtkUtilRetimingSplit( Vec_Str_t * vLags, int fForward )
{
    Vec_Int_t * vNodes;
    Abc_RetStep_t RetStep;
    int Value, i;
    vNodes = Vec_IntAlloc( 100 );
    Vec_StrForEachEntry( vLags, Value, i )
    {
//        assert( Value <= ABC_MAX_EDGE_LATCH );
        if ( Value < 0 && fForward )
        {
            RetStep.iNode = i;
            RetStep.nLatches = -Value;
            Vec_IntPush( vNodes, Abc_RetStep2Int(RetStep) );
        }
        else if ( Value > 0 && !fForward )
        {
            RetStep.iNode = i;
            RetStep.nLatches = Value;
            Vec_IntPush( vNodes, Abc_RetStep2Int(RetStep) );
        }
    }
    return vNodes;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


