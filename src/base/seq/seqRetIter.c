/**CFile****************************************************************

  FileName    [seqRetIter.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Construction and manipulation of sequential AIGs.]

  Synopsis    [The iterative L-Value computation for retiming procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: seqRetIter.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "seqInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// the internal procedures
static int Seq_RetimeSearch_rec( Abc_Ntk_t * pNtk, int FiMin, int FiMax, int fVerbose );
static int Seq_RetimeForPeriod( Abc_Ntk_t * pNtk, int Fi, int fVerbose );
static int Seq_RetimeNodeUpdateLValue( Abc_Obj_t * pObj, int Fi );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Retimes AIG for optimal delay using Pan's algorithm.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Seq_NtkRetimeDelayLags( Abc_Ntk_t * pNtk, int fVerbose )
{
    Abc_Seq_t * p = pNtk->pManFunc;
    Abc_Obj_t * pNode;
    int i, FiMax, FiBest, RetValue;
    char NodeLag;

    assert( Abc_NtkIsSeq( pNtk ) );

    // get the upper bound on the clock period
//    FiMax = Abc_NtkNodeNum(pNtk);
    FiMax = 0;
    Abc_AigForEachAnd( pNtk, pNode, i )
        if ( FiMax < (int)pNode->Level )
            FiMax = pNode->Level;
    FiMax += 2;

    // make sure this clock period is feasible
    assert( Seq_RetimeForPeriod( pNtk, FiMax, fVerbose ) );

    // search for the optimal clock period between 0 and nLevelMax
    FiBest = Seq_RetimeSearch_rec( pNtk, 0, FiMax, fVerbose );

    // recompute the best l-values
    RetValue = Seq_RetimeForPeriod( pNtk, FiBest, fVerbose );
    assert( RetValue );

    // write the retiming lags
    Vec_StrFill( p->vLags, p->nSize, 0 );
    Abc_AigForEachAnd( pNtk, pNode, i )
    {
        NodeLag = Seq_NodeComputeLag( Seq_NodeGetLValue(pNode), FiBest );
        Seq_NodeSetLag( pNode, NodeLag );
    }
/*
    {
        Abc_Obj_t * pFanin, * pFanout;
        pNode = Abc_NtkObj( pNtk, 823 );
        printf( "Node  %d.  Lag = %d. LValue = %d. Latches = (%d,%d) (%d,%d).\n", pNode->Id, Seq_NodeGetLag(pNode), Seq_NodeGetLValue(pNode), 
            Seq_ObjFaninL0(pNode), Seq_ObjFaninL1(pNode), Seq_ObjFanoutL(pNode, Abc_NtkObj(pNtk, 826)), Seq_ObjFanoutL(pNode, Abc_NtkObj(pNtk, 1210)) );
        pFanin = Abc_ObjFanin0( pNode );
        printf( "Fanin %d.  Lag = %d. LValue = %d. Latches = (%d,%d)\n", pFanin->Id, Seq_NodeGetLag(pFanin), Seq_NodeGetLValue(pFanin),
            Seq_ObjFaninL0(pFanin), Seq_ObjFaninL1(pFanin) );
        pFanin = Abc_ObjFanin1( pNode );
        printf( "Fanin %d.  Lag = %d. LValue = %d.\n", pFanin->Id, Seq_NodeGetLag(pFanin), Seq_NodeGetLValue(pFanin) );
        Abc_ObjForEachFanout( pNode, pFanout, i )
            printf( "Fanout %d.  Lag = %d. LValue = %d.\n", pFanout->Id, Seq_NodeGetLag(pFanout), Seq_NodeGetLValue(pFanout) );
        Abc_ObjForEachFanout( Abc_ObjFanin0(pNode), pFanout, i )
            printf( "Fanout %d.  Lag = %d. LValue = %d.\n", pFanout->Id, Seq_NodeGetLag(pFanout), Seq_NodeGetLValue(pFanout) );
    }
*/

    // print the result
    if ( fVerbose )
    printf( "The best clock period is %3d.\n", FiBest );

/*
    printf( "LValues : " );
    Abc_AigForEachAnd( pNtk, pNode, i )
        printf( "%d=%d ", i, Seq_NodeGetLValue(pNode) );
    printf( "\n" );
    printf( "Lags : " );
    Abc_AigForEachAnd( pNtk, pNode, i )
        if ( Vec_StrEntry(p->vLags,i) != 0 )
            printf( "%d=%d(%d)(%d) ", i, Vec_StrEntry(p->vLags,i), Seq_NodeGetLValue(pNode), Seq_NodeGetLValue(pNode) - FiBest * Vec_StrEntry(p->vLags,i) );
    printf( "\n" );
*/
}

/**Function*************************************************************

  Synopsis    [Performs binary search for the optimal clock period.]

  Description [Assumes that FiMin is infeasible while FiMax is feasible.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Seq_RetimeSearch_rec( Abc_Ntk_t * pNtk, int FiMin, int FiMax, int fVerbose )
{
    int Median;
    assert( FiMin < FiMax );
    if ( FiMin + 1 == FiMax )
        return FiMax;
    Median = FiMin + (FiMax - FiMin)/2;
    if ( Seq_RetimeForPeriod( pNtk, Median, fVerbose ) )
        return Seq_RetimeSearch_rec( pNtk, FiMin, Median, fVerbose ); // Median is feasible
    else 
        return Seq_RetimeSearch_rec( pNtk, Median, FiMax, fVerbose ); // Median is infeasible
}

/**Function*************************************************************

  Synopsis    [Returns 1 if retiming with this clock period is feasible.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Seq_RetimeForPeriod( Abc_Ntk_t * pNtk, int Fi, int fVerbose )
{
    Abc_Seq_t * p = pNtk->pManFunc;
    Abc_Obj_t * pObj;
    int nMaxSteps = 10;
    int i, c, RetValue, fChange, Counter;
    char * pReason = "";

    // set l-values of all nodes to be minus infinity
    Vec_IntFill( p->vLValues, p->nSize, -ABC_INFINITY );

    // set l-values of constants and PIs
    pObj = Abc_NtkObj( pNtk, 0 );
    Seq_NodeSetLValue( pObj, 0 );
    Abc_NtkForEachPi( pNtk, pObj, i )
        Seq_NodeSetLValue( pObj, 0 );

    // update all values iteratively
    Counter = 0;
    for ( c = 0; c < nMaxSteps; c++ )
    {
        fChange = 0;
        Abc_AigForEachAnd( pNtk, pObj, i )
        {
            if ( Seq_NodeCutMan(pObj) )
                RetValue = Seq_FpgaNodeUpdateLValue( pObj, Fi );
            else
                RetValue = Seq_RetimeNodeUpdateLValue( pObj, Fi );
//printf( "Node = %d. Value = %d. \n", pObj->Id, RetValue );
            Counter++;
            if ( RetValue == SEQ_UPDATE_FAIL )
                break;
            if ( RetValue == SEQ_UPDATE_NO ) 
                continue;
            fChange = 1;
        }
        Abc_NtkForEachPo( pNtk, pObj, i )
        {
            if ( Seq_NodeCutMan(pObj) )
                RetValue = Seq_FpgaNodeUpdateLValue( pObj, Fi );
            else
                RetValue = Seq_RetimeNodeUpdateLValue( pObj, Fi );
//printf( "Node = %d. Value = %d. \n", pObj->Id, RetValue );
            Counter++;
            if ( RetValue == SEQ_UPDATE_FAIL )
                break;
            if ( RetValue == SEQ_UPDATE_NO ) 
                continue;
            fChange = 1;
        }
        if ( RetValue == SEQ_UPDATE_FAIL )
            break;
        if ( fChange == 0 )
            break;
    }
    if ( c == nMaxSteps )
    {
        RetValue = SEQ_UPDATE_FAIL;
        pReason = "(timeout)";
    }

//Abc_NtkForEachObj( pNtk, pObj, i )
//printf( "%d ", Seq_NodeGetLValue(pObj) );
//printf( "\n" );

    // report the results
    if ( fVerbose )
    {
        if ( RetValue == SEQ_UPDATE_FAIL )
            printf( "Period = %3d.  Iterations = %3d.  Updates = %10d.    Infeasible %s\n", Fi, c, Counter, pReason );
        else
            printf( "Period = %3d.  Iterations = %3d.  Updates = %10d.      Feasible\n",    Fi, c, Counter );
    }
    return RetValue != SEQ_UPDATE_FAIL;
}

/**Function*************************************************************

  Synopsis    [Computes the l-value of the node.]

  Description [The node can be internal or a PO.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Seq_RetimeNodeUpdateLValue( Abc_Obj_t * pObj, int Fi )
{
    int lValueNew, lValueOld, lValue0, lValue1;
    assert( !Abc_ObjIsPi(pObj) );
    assert( Abc_ObjFaninNum(pObj) > 0 );
    lValue0 = Seq_NodeGetLValue(Abc_ObjFanin0(pObj)) - Fi * Seq_ObjFaninL0(pObj);
    if ( Abc_ObjIsPo(pObj) )
        return (lValue0 > Fi)? SEQ_UPDATE_FAIL : SEQ_UPDATE_NO;
    if ( Abc_ObjFaninNum(pObj) == 2 )
        lValue1 = Seq_NodeGetLValue(Abc_ObjFanin1(pObj)) - Fi * Seq_ObjFaninL1(pObj);
    else
        lValue1 = -ABC_INFINITY;
    lValueNew = 1 + ABC_MAX( lValue0, lValue1 );
    lValueOld = Seq_NodeGetLValue(pObj);
//    if ( lValueNew == lValueOld )
    if ( lValueNew <= lValueOld )
        return SEQ_UPDATE_NO;
    Seq_NodeSetLValue( pObj, lValueNew );
    return SEQ_UPDATE_YES;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


