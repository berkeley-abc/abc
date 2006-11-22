/**CFile****************************************************************

  FileName    [retLvalue.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Retiming package.]

  Synopsis    [Implementation of Pan's retiming algorithm.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - Oct 31, 2006.]

  Revision    [$Id: retLvalue.c,v 1.00 2006/10/31 00:00:00 alanmi Exp $]

***********************************************************************/

#include "retInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// node status after updating its arrival time
enum { ABC_RET_UPDATE_FAIL, ABC_RET_UPDATE_NO, ABC_RET_UPDATE_YES };

// the internal procedures
static Vec_Int_t * Abc_NtkRetimeGetLags( Abc_Ntk_t * pNtk, int nIterLimit, int fVerbose );
static int         Abc_NtkRetimeUsingLags( Abc_Ntk_t * pNtk, Vec_Int_t * vLags, int fVerbose );
static int         Abc_NtkRetimeSearch_rec( Abc_Ntk_t * pNtk, Vec_Ptr_t * vNodes, int FiMin, int FiMax, int nMaxIters, int fVerbose );
static int         Abc_NtkRetimeForPeriod( Abc_Ntk_t * pNtk, Vec_Ptr_t * vNodes, int Fi, int nMaxIters, int fVerbose );
static int         Abc_NtkRetimeNodeUpdateLValue( Abc_Obj_t * pObj, int Fi );
static Vec_Ptr_t * Abc_NtkRetimeCollect( Abc_Ntk_t * pNtk );

static inline int  Abc_NodeComputeLag( int LValue, int Fi )          { return (LValue + (1<<16)*Fi)/Fi - (1<<16) - (int)(LValue % Fi == 0);     }
static inline int  Abc_NodeGetLValue( Abc_Obj_t * pNode )            { return (int)pNode->pCopy;        }
static inline void Abc_NodeSetLValue( Abc_Obj_t * pNode, int Value ) { pNode->pCopy = (void *)Value;    }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Implements Pan's retiming algorithm.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRetimeLValue( Abc_Ntk_t * pNtk, int nIterLimit, int fVerbose )
{
    Vec_Int_t * vLags;
    int nLatches = Abc_NtkLatchNum(pNtk);
    assert( Abc_NtkIsLogic( pNtk ) );
    // get the lags
    vLags = Abc_NtkRetimeGetLags( pNtk, nIterLimit, fVerbose );
    // compute the retiming
//    Abc_NtkRetimeUsingLags( pNtk, vLags, fVerbose );
    Vec_IntFree( vLags );
    // fix the COs
//    Abc_NtkLogicMakeSimpleCos( pNtk, 0 );
    // check for correctness
    if ( !Abc_NtkCheck( pNtk ) )
        fprintf( stdout, "Abc_NtkRetimeLValue(): Network check has failed.\n" );
    // return the number of latches saved
    return nLatches - Abc_NtkLatchNum(pNtk);
}

/**Function*************************************************************

  Synopsis    [Computes the retiming lags.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_NtkRetimeGetLags( Abc_Ntk_t * pNtk, int nIterLimit, int fVerbose )
{
    Vec_Int_t * vLags;
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pNode;
    int i, FiMax, FiBest, RetValue, clk, clkIter;
    char NodeLag;

    // get the upper bound on the clock period
    FiMax = 10 + Abc_NtkLevel(pNtk);

    // make sure this clock period is feasible
    vNodes = Abc_NtkRetimeCollect(pNtk);
    if ( !Abc_NtkRetimeForPeriod( pNtk, vNodes, FiMax, nIterLimit, fVerbose ) )
    {
        Vec_PtrFree( vNodes );
        printf( "Abc_NtkRetimeGetLags() error: The upper bound on the clock period cannot be computed.\n" );
        return Vec_IntStart( Abc_NtkObjNumMax(pNtk) + 1 );
    }
 
    // search for the optimal clock period between 0 and nLevelMax
clk = clock();
    FiBest = Abc_NtkRetimeSearch_rec( pNtk, vNodes, 0, FiMax, nIterLimit, fVerbose );
clkIter = clock() - clk;

    // recompute the best l-values
    RetValue = Abc_NtkRetimeForPeriod( pNtk, vNodes, FiBest, nIterLimit, fVerbose );
    assert( RetValue );
    Vec_PtrFree( vNodes );

    // fix the problem with non-converged delays
    Abc_NtkForEachNode( pNtk, pNode, i )
        if ( Abc_NodeGetLValue(pNode) < -ABC_INFINITY/2 )
            Abc_NodeSetLValue( pNode, 0 );

    // write the retiming lags
    vLags = Vec_IntStart( Abc_NtkObjNumMax(pNtk) + 1 );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        NodeLag = Abc_NodeComputeLag( Abc_NodeGetLValue(pNode), FiBest );
        Vec_IntWriteEntry( vLags, pNode->Id, NodeLag );
    }

    // print the result
//    if ( fVerbose )
    printf( "The best clock period is %3d. (Currently, network is not modified.)\n", FiBest );
/*
    // print the statistic into a file
    {
        FILE * pTable;
        pTable = fopen( "a/ret__stats.txt", "a+" );
        fprintf( pTable, "%d ", FiBest );
        fclose( pTable );
    }
*/

/*
    printf( "lvalues and lags : " );
    Abc_NtkForEachNode( pNtk, pNode, i )
        printf( "%d=%d(%d) ", pNode->Id, Abc_NodeGetLValue(pNode), Abc_NodeGetLag(pNode) );
    printf( "\n" );
*/
/*
    {
        FILE * pTable;
        pTable = fopen( "a/ret_stats_pan.txt", "a+" );
        fprintf( pTable, "%s ",  pNtk->pName );
        fprintf( pTable, "%d ", FiBest );
        fprintf( pTable, "\n" );
        fclose( pTable );
    }
*/
    return vLags;
}

/**Function*************************************************************

  Synopsis    [Performs binary search for the optimal clock period.]

  Description [Assumes that FiMin is infeasible while FiMax is feasible.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRetimeSearch_rec( Abc_Ntk_t * pNtk, Vec_Ptr_t * vNodes, int FiMin, int FiMax, int nMaxIters, int fVerbose )
{
    int Median;
    assert( FiMin < FiMax );
    if ( FiMin + 1 == FiMax )
        return FiMax;
    Median = FiMin + (FiMax - FiMin)/2;
    if ( Abc_NtkRetimeForPeriod( pNtk, vNodes, Median, nMaxIters, fVerbose ) )
        return Abc_NtkRetimeSearch_rec( pNtk, vNodes, FiMin, Median, nMaxIters, fVerbose ); // Median is feasible
    else 
        return Abc_NtkRetimeSearch_rec( pNtk, vNodes, Median, FiMax, nMaxIters, fVerbose ); // Median is infeasible
}

/**Function*************************************************************

  Synopsis    [Returns 1 if retiming with this clock period is feasible.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRetimeForPeriod( Abc_Ntk_t * pNtk, Vec_Ptr_t * vNodes, int Fi, int nMaxIters, int fVerbose )
{
    Abc_Obj_t * pObj;
    int i, c, fContained, fChange, RetValue, Counter;
    char * pReason = "";

    // set l-values of all nodes to be minus infinity, except PIs and constants
    Abc_NtkForEachObj( pNtk, pObj, i )
        if ( Abc_ObjFaninNum(pObj) == 0 )
            Abc_NodeSetLValue( pObj, 0 );
        else
            Abc_NodeSetLValue( pObj, -ABC_INFINITY );

    // update all values iteratively
    Counter    = 0;
    fContained = 1;
    fChange    = 1;
    for ( c = 0; fContained && fChange && c < nMaxIters; c++ )
    {
        // go through the nodes and detect change
        fChange = 0;
        Vec_PtrForEachEntry( vNodes, pObj, i )
        {
            RetValue = Abc_NtkRetimeNodeUpdateLValue( pObj, Fi );
            if ( RetValue == ABC_RET_UPDATE_FAIL )
            {
                fContained = 0;
                break;
            }
            if ( RetValue == ABC_RET_UPDATE_NO )
                continue;
            // updating happened
            fChange = 1;
            Counter++;
        }
    }
    if ( c == nMaxIters )
    {
        fContained = 0;
        pReason = "(timeout)";
    }
    else
        c++;
    // report the results
    if ( fVerbose )
    {
        if ( !fContained )
            printf( "Period = %3d.  Iterations = %3d.  Updates = %10d.    Infeasible %s\n", Fi, c, Counter, pReason );
        else
            printf( "Period = %3d.  Iterations = %3d.  Updates = %10d.      Feasible\n",    Fi, c, Counter );
    }
/*
    // check if any AND gates have infinite delay
    Counter = 0;
    Abc_NtkForEachNode( pNtk, pObj, i )
        Counter += (Abc_NodeGetLValue(pObj) < -ABC_INFINITY/2);
    if ( Counter > 0 )
        printf( "Warning: %d internal nodes have wrong l-values!\n", Counter );
*/
    return fContained;
}

/**Function*************************************************************

  Synopsis    [Computes the l-value of the node.]

  Description [The node can be internal or a PO.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRetimeNodeUpdateLValue( Abc_Obj_t * pObj, int Fi )
{
    Abc_Obj_t * pFanin;
    int lValueNew, i;
    // terminals
    if ( Abc_ObjFaninNum(pObj) == 0 )
        return ABC_RET_UPDATE_NO;
    // primary outputs
    if ( Abc_ObjIsPo(pObj) )
        return (Abc_NodeGetLValue(Abc_ObjFanin0(pObj)) > Fi)? ABC_RET_UPDATE_FAIL : ABC_RET_UPDATE_NO;
    // other types of objects
    if ( Abc_ObjIsBi(pObj) || Abc_ObjIsBo(pObj) )
        lValueNew = Abc_NodeGetLValue(Abc_ObjFanin0(pObj));
    else if ( Abc_ObjIsLatch(pObj) )
        lValueNew = Abc_NodeGetLValue(Abc_ObjFanin0(pObj)) - Fi;
    else
    {
        assert( Abc_ObjIsNode(pObj) );
        lValueNew = -ABC_INFINITY;
        Abc_ObjForEachFanin( pObj, pFanin, i )
            if ( lValueNew < Abc_NodeGetLValue(pFanin) )
                lValueNew = Abc_NodeGetLValue(pFanin);
        lValueNew++;
    }
    // check if it needs to be updated
    if ( lValueNew <= Abc_NodeGetLValue(pObj) )
        return ABC_RET_UPDATE_NO;
    // update if needed
    Abc_NodeSetLValue( pObj, lValueNew );
    return ABC_RET_UPDATE_YES;
}

/**Function*************************************************************

  Synopsis    [Implements the retiming given as a set of retiming lags.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRetimeUsingLags( Abc_Ntk_t * pNtk, Vec_Int_t * vLags, int fVerbose )
{
    Abc_Obj_t * pObj;
    int fChanges, fForward, nTotalMoves, Lag, Counter, i;
    // iterate over the nodes
    nTotalMoves = 0;
    do {
        fChanges = 0;
        Abc_NtkForEachNode( pNtk, pObj, i )
        {
            Lag = Vec_IntEntry( vLags, pObj->Id );
            if ( !Lag )
                continue;
            fForward = (Lag < 0);
            if ( Abc_NtkRetimeNodeIsEnabled( pObj, fForward ) )
            {
                Abc_NtkRetimeNode( pObj, fForward, 0 );
                fChanges = 1;
                nTotalMoves++;
                Vec_IntAddToEntry( vLags, pObj->Id, fForward? 1 : -1 );
            }
        }
    } while ( fChanges );
    if ( fVerbose )
        printf( "Total latch moves = %d.\n", nTotalMoves );
    // check if there are remaining lags
    Counter = 0;
    Abc_NtkForEachNode( pNtk, pObj, i )
        Counter += (Vec_IntEntry( vLags, pObj->Id ) != 0);
    if ( Counter )
        printf( "Warning! The number of nodes with unrealized lag = %d.\n", Counter );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Collect objects in the topological order from the latch inputs.]

  Description [If flag fOnlyMarked is set, collects only marked nodes.
  Otherwise, collects only unmarked nodes.]
               
  SideEffects []

  SeeAlso     []
 
***********************************************************************/
void Abc_NtkRetimeCollect_rec( Abc_Obj_t * pObj, int fOnlyMarked, Vec_Ptr_t * vNodes )
{
    Abc_Obj_t * pFanin;
    int i;
    // skip collected nodes
    if ( Abc_NodeIsTravIdCurrent(pObj)  )
        return;
    Abc_NodeSetTravIdCurrent(pObj);
    // collect recursively
    if ( fOnlyMarked ^ pObj->fMarkA )
        return;
    // visit the fanins
    Abc_ObjForEachFanin( pObj, pFanin, i )
        Abc_NtkRetimeCollect_rec( pFanin, fOnlyMarked, vNodes );
    // collect non-trivial objects
    if ( Abc_ObjFaninNum(pObj) > 0 )
        Vec_PtrPush( vNodes, pObj );
}

/**Function*************************************************************

  Synopsis    [Collect objects in the topological order using LIs as a cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkRetimeCollect( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pObj, * pFanin;
    int i, k;
    vNodes = Vec_PtrAlloc( 100 );
    // mark the latch inputs
    Abc_NtkForEachLatch( pNtk, pObj, i )
        Abc_ObjFanin0(pObj)->fMarkA = 1;
    // collect nodes in the DFS order from the marked nodes
    Abc_NtkIncrementTravId(pNtk);
    Abc_NtkForEachPo( pNtk, pObj, i )
        Abc_NtkRetimeCollect_rec( pObj, 0, vNodes );
    Abc_NtkForEachLatch( pNtk, pObj, i )
        Abc_ObjForEachFanin( Abc_ObjFanin0(pObj), pFanin, k )
            Abc_NtkRetimeCollect_rec( pFanin, 0, vNodes );
    // collect marked nodes
    Abc_NtkIncrementTravId(pNtk);
    Abc_NtkForEachLatch( pNtk, pObj, i )
        Abc_NtkRetimeCollect_rec( Abc_ObjFanin0(pObj), 1, vNodes );
    // clean the marks
    Abc_NtkForEachLatch( pNtk, pObj, i )
        Abc_ObjFanin0(pObj)->fMarkA = 0;
    return vNodes;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


