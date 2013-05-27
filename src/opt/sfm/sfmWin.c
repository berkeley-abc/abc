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

  Synopsis    [Returns the MFFC size.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sfm_ObjRef_rec( Sfm_Ntk_t * p, int iObj )
{
    int i, iFanin, Value, Count;
    if ( Sfm_ObjIsPi(p, iObj) )
        return 0;
    assert( Sfm_ObjIsNode(p, iObj) );
    Value = Sfm_ObjRefIncrement(p, iObj);
    if ( Value > 1 )
        return 0;
    assert( Value == 1 );
    Count = 1;
    Sfm_ObjForEachFanin( p, iObj, iFanin, i )
        Count += Sfm_ObjRef_rec( p, iFanin );
    return Count;
}
int Sfm_ObjRef( Sfm_Ntk_t * p, int iObj )
{
    int i, iFanin, Count = 1;
    Sfm_ObjForEachFanin( p, iObj, iFanin, i )
        Count += Sfm_ObjRef_rec( p, iFanin );
    return Count;
}
int Sfm_ObjDeref_rec( Sfm_Ntk_t * p, int iObj )
{
    int i, iFanin, Value, Count;
    if ( Sfm_ObjIsPi(p, iObj) )
        return 0;
    assert( Sfm_ObjIsNode(p, iObj) );
    Value = Sfm_ObjRefDecrement(p, iObj);
    if ( Value > 0 )
        return 0;
    assert( Value == 0 );
    Count = 1;
    Sfm_ObjForEachFanin( p, iObj, iFanin, i )
        Count += Sfm_ObjDeref_rec( p, iFanin );
    return Count;
}
int Sfm_ObjDeref( Sfm_Ntk_t * p, int iObj )
{
    int i, iFanin, Count = 1;
    Sfm_ObjForEachFanin( p, iObj, iFanin, i )
        Count += Sfm_ObjDeref_rec( p, iFanin );
    return Count;
}
int Sfm_ObjMffcSize( Sfm_Ntk_t * p, int iObj )
{
    int Count1, Count2;
    if ( Sfm_ObjIsPi(p, iObj) )
        return 0;
    if ( Sfm_ObjFanoutNum(p, iObj) != 1 )
        return 0;
    assert( Sfm_ObjIsNode( p, iObj ) );
    Count1 = Sfm_ObjDeref( p, iObj );
    Count2 = Sfm_ObjRef( p, iObj );
    assert( Count1 == Count2 );
    return Count1;
}

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
    Sfm_ObjForEachFanin( p, iThis, iFanin, i )
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
    Sfm_ObjForEachFanout( p, iNode, iFanout, i )
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
void Sfm_NtkAddDivisors( Sfm_Ntk_t * p, int iNode, int nLevelMax )
{
    int i, iFanout;
    Sfm_ObjForEachFanout( p, iNode, iFanout, i )
    {
        // skip some of the fanouts if the number is large
        if ( p->pPars->nFanoutMax && i > p->pPars->nFanoutMax )
            return;
        // skip TFI nodes, PO nodes, or nodes with high logic level
        if ( Sfm_ObjIsTravIdCurrent(p, iFanout) || Sfm_ObjIsPo(p, iFanout) ||
            (p->pPars->fFixLevel && Sfm_ObjLevel(p, iFanout) >= nLevelMax) )
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

  Synopsis    [Fixed object is useful when it has a non-fixed fanout.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Sfm_ObjIsUseful( Sfm_Ntk_t * p, int iNode )
{
    int i, iFanout;
    if ( !Sfm_ObjIsFixed(p, iNode) )
        return 1;
    Sfm_ObjForEachFanout( p, iNode, iFanout, i )
        if ( !Sfm_ObjIsFixed(p, iFanout) )
            return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Computes structural window.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sfm_NtkCollectTfi_rec( Sfm_Ntk_t * p, int iNode, int nWinSizeMax )
{
    int i, iFanin;
    if ( Sfm_ObjIsTravIdCurrent( p, iNode ) )
        return 0;
    Sfm_ObjSetTravIdCurrent( p, iNode );
    if ( Sfm_ObjIsPi( p, iNode ) )
    {
        Vec_IntPush( p->vLeaves, iNode );
        return 0;
    }
    Sfm_ObjForEachFanin( p, iNode, iFanin, i )
        if ( Sfm_NtkCollectTfi_rec( p, iFanin, nWinSizeMax ) )
            return 1;
    Vec_IntPush( p->vNodes, iNode );
    return nWinSizeMax && (Vec_IntSize(p->vNodes) > nWinSizeMax);
}
int Sfm_NtkCreateWindow( Sfm_Ntk_t * p, int iNode, int fVerbose )
{
    int i, k, iTemp, nDivStart;
    abctime clk = Abc_Clock();
    assert( Sfm_ObjIsNode( p, iNode ) );
    Vec_IntClear( p->vLeaves ); // leaves 
    Vec_IntClear( p->vNodes );  // internal
    Vec_IntClear( p->vDivs );   // divisors
    Vec_IntClear( p->vRoots );  // roots
    Vec_IntClear( p->vTfo );    // roots
    // collect transitive fanin
    Sfm_NtkIncrementTravId( p );
    if ( Sfm_NtkCollectTfi_rec( p, iNode, p->pPars->nWinSizeMax ) )
    {
        p->nMaxDivs++;
        p->timeWin += Abc_Clock() - clk;
        return 0;
    }
    // collect TFO (currently use only one level of TFO)
//    if ( Sfm_NtkCheckFanouts(p, iNode) )
    if ( 0 )
    {
        Sfm_ObjForEachFanout( p, iNode, iTemp, i )
        {
            if ( Sfm_ObjIsPo(p, iTemp) )
                continue;
            Vec_IntPush( p->vRoots, iTemp );
            Vec_IntPush( p->vTfo, iTemp );
        }
    }
    else
        Vec_IntPush( p->vRoots, iNode );
    p->timeWin += Abc_Clock() - clk;
    clk = Abc_Clock();
    // create divisors
    Vec_IntClear( p->vDivs );
    Vec_IntForEachEntry( p->vLeaves, iTemp, i )
        Vec_IntPush( p->vDivs, iTemp );
    Vec_IntForEachEntry( p->vNodes, iTemp, i )
        Vec_IntPush( p->vDivs, iTemp );
    Vec_IntPop( p->vDivs );
    // add non-topological divisors
    nDivStart = Vec_IntSize(p->vDivs);
    if ( Vec_IntSize(p->vDivs) < p->pPars->nWinSizeMax )
    {
        Sfm_NtkIncrementTravId2( p );
        Vec_IntForEachEntry( p->vDivs, iTemp, i )
            if ( Vec_IntSize(p->vDivs) < p->pPars->nWinSizeMax )
                Sfm_NtkAddDivisors( p, iTemp, Sfm_ObjLevel(p, iNode) );
    }
    if ( Vec_IntSize(p->vDivs) > p->pPars->nWinSizeMax )
        Vec_IntShrink( p->vDivs, p->pPars->nWinSizeMax );
    assert( Vec_IntSize(p->vDivs) <= p->pPars->nWinSizeMax );
    p->nMaxDivs += (Vec_IntSize(p->vDivs) == p->pPars->nWinSizeMax);
    // create ordering of the nodes
    Vec_IntClear( p->vOrder );
    Vec_IntForEachEntryReverse( p->vNodes, iTemp, i )
        Vec_IntPush( p->vOrder, iTemp );
    Vec_IntForEachEntry( p->vLeaves, iTemp, i )
        Vec_IntPush( p->vOrder, iTemp );
    Vec_IntForEachEntryStart( p->vDivs, iTemp, i, nDivStart )
        Vec_IntPush( p->vOrder, iTemp );
    // remove fanins from divisors
    // mark fanins
    Sfm_NtkIncrementTravId2( p );
    Sfm_ObjSetTravIdCurrent2( p, iNode );
    Sfm_ObjForEachFanin( p, iNode, iTemp, i )
        Sfm_ObjSetTravIdCurrent2( p, iTemp );
    // compact divisors
    k = 0;
    Vec_IntForEachEntry( p->vDivs, iTemp, i )
        if ( !Sfm_ObjIsTravIdCurrent2(p, iTemp) && Sfm_ObjIsUseful(p, iTemp) )
            Vec_IntWriteEntry( p->vDivs, k++, iTemp );
    Vec_IntShrink( p->vDivs, k );
    assert( Vec_IntSize(p->vDivs) <= p->pPars->nWinSizeMax );
    // statistics
    p->nTotalDivs += Vec_IntSize(p->vDivs);
    p->timeDiv += Abc_Clock() - clk;
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
        Sfm_NtkCreateWindow( p, i, 1 );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

