/**CFile****************************************************************

  FileName    [sfmWin.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based optimization using internal don't-cares.]

  Synopsis    [Structural window computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: sfmWin.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sfmInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Working with traversal IDs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void  Sfm_NtkIncrementTravId( Sfm_Ntk_t * p )            { p->nTravIds++;                                            }       
static inline void  Sfm_ObjSetTravIdCurrent( Sfm_Ntk_t * p, int Id )   { Vec_IntWriteEntry( &p->vTravIds, Id, p->nTravIds );       }
static inline int   Sfm_ObjIsTravIdCurrent( Sfm_Ntk_t * p, int Id )    { return (Vec_IntEntry(&p->vTravIds, Id) == p->nTravIds);   }   

static inline void  Sfm_NtkIncrementTravId2( Sfm_Ntk_t * p )           { p->nTravIds2++;                                           }       
static inline void  Sfm_ObjSetTravIdCurrent2( Sfm_Ntk_t * p, int Id )  { Vec_IntWriteEntry( &p->vTravIds2, Id, p->nTravIds2 );     }
static inline int   Sfm_ObjIsTravIdCurrent2( Sfm_Ntk_t * p, int Id )   { return (Vec_IntEntry(&p->vTravIds2, Id) == p->nTravIds2); }   


/**Function*************************************************************

  Synopsis    [Check if this fanout overlaps with TFI cone of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sfm_NtkCheckOverlap_rec( Sfm_Ntk_t * p, int iThis, int iNode )
{
    int i, iFanin;
    if ( Sfm_ObjIsTravIdCurrent2(p, iThis) || iThis == iNode )
        return 0;
    if ( Sfm_ObjIsTravIdCurrent(p, iThis) )
        return 1;
    Sfm_ObjSetTravIdCurrent2(p, iThis);
    Sfm_NodeForEachFanin( p, iThis, iFanin, i )
        if ( Sfm_NtkCheckOverlap_rec(p, iFanin, iNode) )
            return 1;
    return 0;
}
int Sfm_NtkCheckOverlap( Sfm_Ntk_t * p, int iFan, int iNode )
{
    Sfm_NtkIncrementTravId2( p );
    return Sfm_NtkCheckOverlap_rec( p, iFan, iNode );
}

/**Function*************************************************************

  Synopsis    [Check fanouts of the node.]

  Description [Returns 1 if they can be used instead of the node.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sfm_NtkCheckFanouts( Sfm_Ntk_t * p, int iNode )
{
    int i, iFanout;
    if ( Sfm_ObjFanoutNum(p, iNode) >= p->pPars->nFanoutMax )
        return 0;
    Sfm_NodeForEachFanout( p, iNode, iFanout, i )
        if ( !Sfm_NtkCheckOverlap( p, iFanout, iNode ) )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Collects divisors of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_NtkAddDivisors( Sfm_Ntk_t * p, int iNode )
{
    int i, iFanout;
    Sfm_NodeForEachFanout( p, iNode, iFanout, i )
    {
        // skip TFI nodes, PO nodes, and nodes with high fanout or nodes with high logic level
        if ( Sfm_ObjIsTravIdCurrent(p, iFanout) || Sfm_ObjIsPo(p, iFanout) || 
            Sfm_ObjFanoutNum(p, iFanout) >= p->pPars->nFanoutMax ||
            (p->pPars->fFixLevel && Sfm_ObjLevel(p, iFanout) >= Sfm_ObjLevel(p, iNode)) )
            continue;
        // handle single-input nodes
        if ( Sfm_ObjFaninNum(p, iFanout) == 1 )
            Vec_IntPush( p->vDivs, iFanout );
        // visit node for the first time
        else if ( !Sfm_ObjIsTravIdCurrent2(p, iFanout) )
        {
            assert( Sfm_ObjFaninNum(p, iFanout) > 1 );
            Sfm_ObjSetTravIdCurrent2( p, iFanout );
            Sfm_ObjResetFaninCount( p, iFanout );
        }
        // visit node again
        else if ( Sfm_ObjUpdateFaninCount(p, iFanout) == 0 )
            Vec_IntPush( p->vDivs, iFanout );
    }
}

/**Function*************************************************************

  Synopsis    [Computes structural window.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_NtkCollectTfi_rec( Sfm_Ntk_t * p, int iNode )
{
    int i, iFanin;
    if ( Sfm_ObjIsTravIdCurrent( p, iNode ) )
        return;
    Sfm_ObjSetTravIdCurrent( p, iNode );
    if ( Sfm_ObjIsPi( p, iNode ) )
    {
        Vec_IntPush( p->vLeaves, iNode );
        return;
    }
    Sfm_NodeForEachFanin( p, iNode, iFanin, i )
        Sfm_NtkCollectTfi_rec( p, iFanin );
    Vec_IntPush( p->vNodes, iNode );
}
int Sfm_NtkWindow( Sfm_Ntk_t * p, int iNode, int fVerbose )
{
    int i, iTemp;
/*
    if ( iNode == 7 )
    {
        int iLevel = Sfm_ObjLevel(p, iNode);
        int s = 0;
    }
*/
    assert( Sfm_ObjIsNode( p, iNode ) );
    Vec_IntClear( p->vLeaves ); // leaves 
    Vec_IntClear( p->vNodes );  // internal
    // collect transitive fanin
    Sfm_NtkIncrementTravId( p );
    Sfm_NtkCollectTfi_rec( p, iNode );
    // collect TFO (currently use only one level of TFO)
    Vec_IntClear( p->vRoots );  // roots
    Vec_IntClear( p->vTfo );    // roots
    if ( Sfm_NtkCheckFanouts(p, iNode) )
    {
        Sfm_NodeForEachFanout( p, iNode, iTemp, i )
        {
            if ( Sfm_ObjIsPo(p, iTemp) )
                continue;
            Vec_IntPush( p->vRoots, iTemp );
            Vec_IntPush( p->vTfo, iTemp );
        }
    }
    else
        Vec_IntPush( p->vRoots, iNode );
    // collect divisors of the TFI nodes
    Vec_IntClear( p->vDivs );
    Sfm_NtkIncrementTravId2( p );
    Vec_IntForEachEntry( p->vLeaves, iTemp, i )
        Sfm_NtkAddDivisors( p, iTemp );
    Vec_IntForEachEntry( p->vNodes, iTemp, i )
        Sfm_NtkAddDivisors( p, iTemp );
    Vec_IntForEachEntry( p->vDivs, iTemp, i )
        Sfm_NtkAddDivisors( p, iTemp );
    if ( !fVerbose )
        return 1;

    // print stats about the window
    printf( "%6d : ", iNode );
    printf( "Leaves = %5d. ", Vec_IntSize(p->vLeaves) );
    printf( "Nodes = %5d. ",  Vec_IntSize(p->vNodes) );
    printf( "Roots = %5d. ",  Vec_IntSize(p->vRoots) );
    printf( "Divs = %5d. ",   Vec_IntSize(p->vDivs) );
    printf( "\n" );
    return 1;
}
void Sfm_NtkWindowTest( Sfm_Ntk_t * p, int iNode )
{
    int i;
    Sfm_NtkForEachNode( p, i )
        Sfm_NtkWindow( p, i, 1 );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

