/**CFile****************************************************************

  FileName    [abcSeqRetime.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Peforms retiming for optimal clock cycle.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcSeqRetime.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abcs.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// the internal procedures
static int Abc_NtkRetimeSearch_rec( Abc_Ntk_t * pNtk, int FiMin, int FiMax, int fVerbose );
static int Abc_NtkRetimeForPeriod( Abc_Ntk_t * pNtk, int Fi, int fVerbose );
static int Abc_NodeUpdateLValue( Abc_Obj_t * pObj, int Fi );

// node status after updating its arrival time
enum { ABC_UPDATE_FAIL, ABC_UPDATE_NO, ABC_UPDATE_YES };

static void Abc_RetimingExperiment( Abc_Ntk_t * pNtk, Vec_Str_t * vLags );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Retimes AIG for optimal delay.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Str_t * Abc_NtkSeqRetimeDelayLags( Abc_Ntk_t * pNtk, int fVerbose )
{
    Vec_Str_t * vLags;
    Abc_Obj_t * pNode;
    int i, FiMax, FiBest, RetValue;
    assert( Abc_NtkIsSeq( pNtk ) );

    // start storage for sequential arrival times
    assert( pNtk->pData == NULL );
    pNtk->pData = Vec_IntAlloc( 0 );

    // get the upper bound on the clock period
//    FiMax = Abc_NtkNodeNum(pNtk);
    FiMax = 0;
    Abc_AigForEachAnd( pNtk, pNode, i )
        if ( FiMax < (int)pNode->Level )
            FiMax = pNode->Level;
    FiMax += 2;

    // make sure this clock period is feasible
    assert( Abc_NtkRetimeForPeriod( pNtk, FiMax, fVerbose ) );

    // search for the optimal clock period between 0 and nLevelMax
    FiBest = Abc_NtkRetimeSearch_rec( pNtk, 0, FiMax, fVerbose );

    // recompute the best LValues
    RetValue = Abc_NtkRetimeForPeriod( pNtk, FiBest, fVerbose );
    assert( RetValue );

    // print the result
    if ( fVerbose )
    printf( "The best clock period is %3d.\n", FiBest );

    // convert to lags
    vLags = Vec_StrStart( Abc_NtkObjNumMax(pNtk) );
    Abc_AigForEachAnd( pNtk, pNode, i )
        Vec_StrWriteEntry( vLags, i, (char)Abc_NodeGetLag(Abc_NodeReadLValue(pNode), FiBest) );
/*
    printf( "LValues : " );
    Abc_AigForEachAnd( pNtk, pNode, i )
        printf( "%d=%d ", i, Abc_NodeReadLValue(pNode) );
    printf( "\n" );
    printf( "Lags : " );
    Abc_AigForEachAnd( pNtk, pNode, i )
        if ( Vec_StrEntry(vLags,i) != 0 )
            printf( "%d=%d(%d)(%d) ", i, Vec_StrEntry(vLags,i), Abc_NodeReadLValue(pNode), Abc_NodeReadLValue(pNode) - FiBest * Vec_StrEntry(vLags,i) );
    printf( "\n" );
*/

    // free storage
    Vec_IntFree( pNtk->pData );
    pNtk->pData = NULL;
    return vLags;
}

/**Function*************************************************************

  Synopsis    [Performs binary search for the optimal clock period.]

  Description [Assumes that FiMin is infeasible while FiMax is feasible.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRetimeSearch_rec( Abc_Ntk_t * pNtk, int FiMin, int FiMax, int fVerbose )
{
    int Median;
    assert( FiMin < FiMax );
    if ( FiMin + 1 == FiMax )
        return FiMax;
    Median = FiMin + (FiMax - FiMin)/2;
    if ( Abc_NtkRetimeForPeriod( pNtk, Median, fVerbose ) )
        return Abc_NtkRetimeSearch_rec( pNtk, FiMin, Median, fVerbose ); // Median is feasible
    else 
        return Abc_NtkRetimeSearch_rec( pNtk, Median, FiMax, fVerbose ); // Median is infeasible
}

/**Function*************************************************************

  Synopsis    [Returns 1 if retiming with this clock period is feasible.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRetimeForPeriod2( Abc_Ntk_t * pNtk, int Fi )
{
    Vec_Ptr_t * vFrontier;
    Abc_Obj_t * pObj, * pFanout;
    char * pReason = "";
    int RetValue, i, k;
    int Limit;

    // set l-values of all nodes to be minus infinity
    Vec_IntFill( pNtk->pData, Abc_NtkObjNumMax(pNtk), -ABC_INFINITY );

    // start the frontier by setting PI l-values to 0 and including PI fanouts
    vFrontier = Vec_PtrAlloc( 100 );
    pObj = Abc_NtkObj( pNtk, 0 );
    if ( Abc_ObjFanoutNum(pObj) > 0 )
    {
        Abc_NodeSetLValue( pObj, 0 );
        Abc_ObjForEachFanout( pObj, pFanout, k )
            if ( pFanout->fMarkA == 0 )
            {   
                Vec_PtrPush( vFrontier, pFanout );
                pFanout->fMarkA = 1;
            }
    }
    Abc_NtkForEachPi( pNtk, pObj, i )
    {
        Abc_NodeSetLValue( pObj, 0 );
        Abc_ObjForEachFanout( pObj, pFanout, k )
            if ( pFanout->fMarkA == 0 )
            {   
                Vec_PtrPush( vFrontier, pFanout );
                pFanout->fMarkA = 1;
            }
    }

    // iterate until convergence
    Limit = Abc_NtkObjNumMax(pNtk) * 20;
    Vec_PtrForEachEntry( vFrontier, pObj, i )
    {
        pObj->fMarkA = 0;
        RetValue = Abc_NodeUpdateLValue( pObj, Fi );
        if ( RetValue == ABC_UPDATE_FAIL )
            break;
        if ( i == Limit )
        {
            RetValue = ABC_UPDATE_FAIL;
            pReason = "(timeout)";
            break;
        }
        if ( RetValue == ABC_UPDATE_NO ) 
            continue;
        assert( RetValue == ABC_UPDATE_YES );
        // arrival times have changed - add fanouts to the frontier
        Abc_ObjForEachFanout( pObj, pFanout, k )
            if ( pFanout->fMarkA == 0 && pFanout != pObj )
            {   
                Vec_PtrPush( vFrontier, pFanout );
                pFanout->fMarkA = 1;
            }
    }
    // clean the nodes
    Vec_PtrForEachEntryStart( vFrontier, pObj, k, i )
        pObj->fMarkA = 0;

  // report the results
    if ( RetValue == ABC_UPDATE_FAIL )
        printf( "Period = %3d.  Updated nodes = %6d.    Infeasible %s\n", Fi, vFrontier->nSize, pReason );
    else
        printf( "Period = %3d.  Updated nodes = %6d.    Feasible\n",   Fi, vFrontier->nSize );
    Vec_PtrFree( vFrontier );
    return RetValue != ABC_UPDATE_FAIL;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if retiming with this clock period is feasible.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRetimeForPeriod( Abc_Ntk_t * pNtk, int Fi, int fVerbose )
{
    Abc_Obj_t * pObj;
    int i, c, RetValue, fChange, Counter;
    char * pReason = "";

    // set l-values of all nodes to be minus infinity
    Vec_IntFill( pNtk->pData, Abc_NtkObjNumMax(pNtk), -ABC_INFINITY );

    // set l-values for the constant and PIs
    pObj = Abc_NtkObj( pNtk, 0 );
    Abc_NodeSetLValue( pObj, 0 );
    Abc_NtkForEachPi( pNtk, pObj, i )
        Abc_NodeSetLValue( pObj, 0 );

    // update all values iteratively
    Counter = 0;
    for ( c = 0; c < 20; c++ )
    {
        fChange = 0;
        Abc_NtkForEachObj( pNtk, pObj, i )
        {
            if ( Abc_ObjIsPi(pObj) )
                continue;
            if ( Abc_ObjFaninNum(pObj) == 0 )
                continue;
            RetValue = Abc_NodeUpdateLValue( pObj, Fi );
            Counter++;
            if ( RetValue == ABC_UPDATE_FAIL )
                break;
            if ( RetValue == ABC_UPDATE_NO ) 
                continue;
            fChange = 1;
        }
        if ( RetValue == ABC_UPDATE_FAIL )
            break;
        if ( fChange == 0 )
            break;
    }
    if ( c == 20 )
    {
        RetValue = ABC_UPDATE_FAIL;
        pReason = "(timeout)";
    }

    // report the results
    if ( fVerbose )
    {
        if ( RetValue == ABC_UPDATE_FAIL )
            printf( "Period = %3d.  Iterations = %3d.  Updates = %6d.  Infeasible %s\n", Fi, c, Counter, pReason );
        else
            printf( "Period = %3d.  Iterations = %3d.  Updates = %6d.  Feasible\n",   Fi, c, Counter );
    }
    return RetValue != ABC_UPDATE_FAIL;
}

/**Function*************************************************************

  Synopsis    [Computes the l-value of the node.]

  Description [The node can be internal or a PO.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeUpdateLValue( Abc_Obj_t * pObj, int Fi )
{
    int lValueNew, lValueOld, lValue0, lValue1;
    assert( !Abc_ObjIsPi(pObj) );
    assert( Abc_ObjFaninNum(pObj) > 0 );
    lValue0 = Abc_NodeReadLValue(Abc_ObjFanin0(pObj)) - Fi * Abc_ObjFaninL0(pObj);
    if ( Abc_ObjIsPo(pObj) )
        return (lValue0 > Fi)? ABC_UPDATE_FAIL : ABC_UPDATE_NO;
    if ( Abc_ObjFaninNum(pObj) == 2 )
        lValue1 = Abc_NodeReadLValue(Abc_ObjFanin1(pObj)) - Fi * Abc_ObjFaninL1(pObj);
    else
        lValue1 = -ABC_INFINITY;
    lValueNew = 1 + ABC_MAX( lValue0, lValue1 );
    lValueOld = Abc_NodeReadLValue(pObj);
//    if ( lValueNew == lValueOld )
    if ( lValueNew <= lValueOld )
        return ABC_UPDATE_NO;
    Abc_NodeSetLValue( pObj, lValueNew );
    return ABC_UPDATE_YES;
}





/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_RetimingPrint_rec( Abc_Obj_t * pObj )
{
    Abc_Obj_t * pFanin0, * pFanin1;
    int Depth0, Depth1;

    if ( Abc_ObjIsPi(pObj) )
    {
        printf( "%d -> ", pObj->Id );
        return 0;
    }
    
    pFanin0 = Abc_ObjFanin0(pObj);
    pFanin1 = Abc_ObjFanin1(pObj);

    if ( Abc_ObjFaninL0(pObj) == 0 && Abc_ObjFaninL1(pObj) > 0 )
        Abc_RetimingPrint_rec( pFanin0 );
    else if ( Abc_ObjFaninL1(pObj) == 0 && Abc_ObjFaninL0(pObj) > 0 )
        Abc_RetimingPrint_rec( pFanin1 );
    else if ( Abc_ObjFaninL0(pObj) == 0 && Abc_ObjFaninL1(pObj) == 0 )
    {
        Depth0 = (int)pFanin0->pCopy;
        Depth1 = (int)pFanin1->pCopy;

        if ( Depth0 > Depth1 )
            Abc_RetimingPrint_rec( pFanin0 );
        else
            Abc_RetimingPrint_rec( pFanin1 );
    }

    printf( "%d (%d) -> ", pObj->Id, (int)pObj->pCopy );
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_Retiming_rec( Abc_Obj_t * pObj )
{
    int Depth0, Depth1, Depth;
    if ( Abc_ObjIsPi(pObj) )
    {
        pObj->pCopy = 0;
        return 0;
    }
    // if this node is already visited, skip
    if ( Abc_NodeIsTravIdCurrent( pObj ) )
        return (int)pObj->pCopy;
    // mark the node as visited
    Abc_NodeSetTravIdCurrent( pObj );
    if ( Abc_ObjFaninL0(pObj) == 0 )
        Depth0 = Abc_Retiming_rec( Abc_ObjFanin0(pObj) );
    else
        Depth0 = 0;
    if ( Abc_ObjFaninL1(pObj) == 0 )
        Depth1 = Abc_Retiming_rec( Abc_ObjFanin1(pObj) );
    else
        Depth1 = 0;
    Depth = 1 + ABC_MAX( Depth0, Depth1 );
    pObj->pCopy = (void *)Depth;
    return Depth;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRetiming( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pObj;
    int i, Depth;
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        if ( Abc_ObjFaninNum(pObj) != 2 )
            continue;
        if ( Abc_ObjFaninL0(pObj) > 0 )
        {
            Abc_NtkIncrementTravId(pNtk);
            Depth = Abc_Retiming_rec( Abc_ObjFanin0(pObj) );
            if ( Depth > 30 )
            {
                printf( "Depth is %d.   ", Depth );
                Abc_RetimingPrint_rec( Abc_ObjFanin0(pObj) );
                printf( "\n\n" );
            }
        }
        if ( Abc_ObjFaninL1(pObj) > 0 )
        {
            Abc_NtkIncrementTravId(pNtk);
            Depth = Abc_Retiming_rec( Abc_ObjFanin1(pObj) );
            if ( Depth > 30 )
            {
                printf( "Depth is %d.   ", Depth );
                Abc_RetimingPrint_rec( Abc_ObjFanin1(pObj) );
                printf( "\n\n" );
            }
        }
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_RetimingExperiment( Abc_Ntk_t * pNtk, Vec_Str_t * vLags )
{
    Abc_Obj_t * pObj;
    char Lag;
    int i;

    Vec_StrForEachEntry( vLags, Lag, i )
    {
        if ( Lag == 0 )
            continue;
        pObj = Abc_NtkObj( pNtk, i );
        if ( Lag < 0 )
            Abc_ObjRetimeForwardTry( pObj, -Lag );
        else
            Abc_ObjRetimeBackwardTry( pObj, Lag );
    }

    // make sure there are no negative latches
    Abc_NtkForEachObj( pNtk, pObj, i )
    {
        if ( Abc_ObjFaninNum(pObj) == 0 )
            continue;
        assert( Abc_ObjFaninL0(pObj) >= 0 );
        if ( Abc_ObjFaninNum(pObj) == 1 )
            continue;
        assert( Abc_ObjFaninL1(pObj) >= 0 );
//        printf( "%d=(%d,%d) ", i, Abc_ObjFaninL0(pObj), Abc_ObjFaninL1(pObj) );
    }
//    printf( "\n" );

    Abc_NtkRetiming( pNtk );

    Vec_StrForEachEntry( vLags, Lag, i )
    {
        if ( Lag == 0 )
            continue;
        pObj = Abc_NtkObj( pNtk, i );
        if ( Lag < 0 )
            Abc_ObjRetimeBackwardTry( pObj, -Lag );
        else
            Abc_ObjRetimeForwardTry( pObj, Lag );
    }

//    Abc_NtkSeqRetimeDelayLags( pNtk );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

