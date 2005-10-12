/**CFile****************************************************************

  FileName    [abcFpgaDelay.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Utilities working sequential AIGs.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcFpgaDelay.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abcs.h"
#include "cut.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// the internal procedures
static int  Abc_NtkFpgaRetimeSearch_rec( Seq_FpgaMan_t * p, Abc_Ntk_t * pNtk, int FiMin, int FiMax, int fVerbose );
static int  Abc_NtkFpgaRetimeForPeriod( Seq_FpgaMan_t * p, Abc_Ntk_t * pNtk, int Fi, int fVerbose );
static int  Abc_NodeFpgaUpdateLValue( Seq_FpgaMan_t * p, Abc_Obj_t * pObj, int Fi );
static void Abc_NtkFpgaCollect( Seq_FpgaMan_t * p );

// node status after updating its arrival time
enum { ABC_FPGA_UPDATE_FAIL, ABC_FPGA_UPDATE_NO, ABC_FPGA_UPDATE_YES };

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Retimes AIG for optimal delay.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkFpgaSeqRetimeDelayLags( Seq_FpgaMan_t * p )
{
    Abc_Ntk_t * pNtk = p->pNtk;
    int fVerbose = p->fVerbose;
    Abc_Obj_t * pNode;
    int i, FiMax, FiBest, RetValue;

    // start storage for sequential arrival times
    assert( pNtk->pData == NULL );
    pNtk->pData = p->vArrivals;

    // get the upper bound on the clock period
//    FiMax = Abc_NtkNodeNum(pNtk);
    FiMax = 0;
    Abc_AigForEachAnd( pNtk, pNode, i )
        if ( FiMax < (int)pNode->Level )
            FiMax = pNode->Level;
    FiMax += 2;

    // make sure this clock period is feasible
    assert( Abc_NtkFpgaRetimeForPeriod( p, pNtk, FiMax, fVerbose ) );

    // search for the optimal clock period between 0 and nLevelMax
    FiBest = Abc_NtkFpgaRetimeSearch_rec( p, pNtk, 0, FiMax, fVerbose );

    // recompute the best LValues
    RetValue = Abc_NtkFpgaRetimeForPeriod( p, pNtk, FiBest, fVerbose );
    assert( RetValue );

    // print the result
    if ( fVerbose )
    printf( "The best clock period is %3d.\n", FiBest );

    // convert to lags
    Abc_AigForEachAnd( pNtk, pNode, i )
        Vec_StrWriteEntry( p->vLagsMap, i, (char)Abc_NodeGetLag(Abc_NodeReadLValue(pNode), FiBest) );
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
    Abc_NtkFpgaCollect( p );

    pNtk->pData = NULL;

    Cut_ManStop( p->pMan );
    p->pMan = NULL;
}

/**Function*************************************************************

  Synopsis    [Performs binary search for the optimal clock period.]

  Description [Assumes that FiMin is infeasible while FiMax is feasible.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkFpgaRetimeSearch_rec( Seq_FpgaMan_t * p, Abc_Ntk_t * pNtk, int FiMin, int FiMax, int fVerbose )
{
    int Median;
    assert( FiMin < FiMax );
    if ( FiMin + 1 == FiMax )
        return FiMax;
    Median = FiMin + (FiMax - FiMin)/2;
    if ( Abc_NtkFpgaRetimeForPeriod( p, pNtk, Median, fVerbose ) )
        return Abc_NtkFpgaRetimeSearch_rec( p, pNtk, FiMin, Median, fVerbose ); // Median is feasible
    else 
        return Abc_NtkFpgaRetimeSearch_rec( p, pNtk, Median, FiMax, fVerbose ); // Median is infeasible
}

/**Function*************************************************************

  Synopsis    [Returns 1 if retiming with this clock period is feasible.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkFpgaRetimeForPeriod( Seq_FpgaMan_t * p, Abc_Ntk_t * pNtk, int Fi, int fVerbose )
{
    Abc_Obj_t * pObj;
    int i, c, RetValue, fChange, Counter;
    char * pReason = "";

    // set l-values of all nodes to be minus infinity
    Vec_IntFill( p->vArrivals, Abc_NtkObjNumMax(pNtk), -ABC_INFINITY );
    Vec_PtrFill( p->vBestCuts, Abc_NtkObjNumMax(pNtk),  NULL         );

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
            RetValue = Abc_NodeFpgaUpdateLValue( p, pObj, Fi );
            Counter++;
            if ( RetValue == ABC_FPGA_UPDATE_FAIL )
                break;
            if ( RetValue == ABC_FPGA_UPDATE_NO ) 
                continue;
            fChange = 1;
        }
        if ( RetValue == ABC_FPGA_UPDATE_FAIL )
            break;
        if ( fChange == 0 )
            break;
    }
    if ( c == 20 )
    {
        RetValue = ABC_FPGA_UPDATE_FAIL;
        pReason = "(timeout)";
    }

    // report the results
    if ( fVerbose )
    {
        if ( RetValue == ABC_FPGA_UPDATE_FAIL )
            printf( "Period = %3d.  Iterations = %3d.  Updates = %6d.  Infeasible %s\n", Fi, c, Counter, pReason );
        else
            printf( "Period = %3d.  Iterations = %3d.  Updates = %6d.  Feasible\n",   Fi, c, Counter );
    }
    return RetValue != ABC_FPGA_UPDATE_FAIL;
}

/**Function*************************************************************

  Synopsis    [Computes the l-value of the node.]

  Description [The node can be internal or a PO.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeFpgaUpdateLValue( Seq_FpgaMan_t * p, Abc_Obj_t * pObj, int Fi )
{
    Abc_Obj_t * pFanin;
    Cut_Cut_t * pList, * pCut, * pCutBest;
    int lValueNew, lValueOld, lValueCur, lValueFan;
    int i;

    assert( !Abc_ObjIsPi(pObj) );
    assert( Abc_ObjFaninNum(pObj) > 0 );

    if ( Abc_ObjIsPo(pObj) )
    {
        lValueOld = Abc_NodeReadLValue(Abc_ObjFanin0(pObj));
        lValueNew = lValueOld - Fi * Abc_ObjFaninL0(pObj);
        return (lValueNew > Fi)? ABC_FPGA_UPDATE_FAIL : ABC_FPGA_UPDATE_NO;
    }

    pCutBest = NULL;
    lValueNew = ABC_INFINITY;
    pList = Abc_NodeReadCuts( p->pMan, pObj );
    for ( pCut = pList; pCut; pCut = pCut->pNext )
    {
        if ( pCut->nLeaves < 2 )
            continue;
        lValueCur = -ABC_INFINITY;
        for ( i = 0; i < (int)pCut->nLeaves; i++ )
        {
            pFanin    = Abc_NtkObj( pObj->pNtk, (pCut->pLeaves[i] >> CUT_SHIFT) );
            lValueFan = Abc_NodeReadLValue(pFanin) - Fi * (pCut->pLeaves[i] & CUT_MASK);
            lValueCur = ABC_MAX( lValueCur, lValueFan );
        }
        lValueCur += 1;
        lValueNew = ABC_MIN( lValueNew, lValueCur );
        if ( lValueNew == lValueCur )
            pCutBest = pCut;
    }

    lValueOld = Abc_NodeReadLValue(pObj);
//    if ( lValueNew == lValueOld )
    if ( lValueNew <= lValueOld )
        return ABC_FPGA_UPDATE_NO;

    Abc_NodeSetLValue( pObj, lValueNew );
    Vec_PtrWriteEntry( p->vBestCuts, pObj->Id, pCutBest );
    return ABC_FPGA_UPDATE_YES;
}



/**Function*************************************************************

  Synopsis    [Select nodes visible in the mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeFpgaCollect_rec( Seq_FpgaMan_t * p, Abc_Obj_t * pNode )
{
    Cut_Cut_t * pCutBest;
    Abc_Obj_t * pFanin;
    Vec_Int_t * vLeaves;
    int i;
    // skip the CI
    if ( Abc_ObjIsCi(pNode) )
        return;
    // if this node is already visited, skip
    if ( Abc_NodeIsTravIdCurrent( pNode ) )
        return;
    // mark the node as visited
    Abc_NodeSetTravIdCurrent( pNode );
    // get the best cut of the node
    pCutBest = Vec_PtrEntry( p->vBestCuts, pNode->Id );
    for ( i = 0; i < (int)pCutBest->nLeaves; i++ )
    {
        pFanin = Abc_NtkObj( pNode->pNtk, (pCutBest->pLeaves[i] >> CUT_SHIFT) );
        Abc_NodeFpgaCollect_rec( p, pFanin );
    }
    // collect the node and its cut
    vLeaves = Vec_IntAlloc( pCutBest->nLeaves );
    for ( i = 0; i < (int)pCutBest->nLeaves; i++ )
        Vec_IntPush( vLeaves, pCutBest->pLeaves[i] );
    Vec_PtrPush( p->vMapCuts, vLeaves );
    Vec_PtrPush( p->vMapping, pNode );
}

/**Function*************************************************************

  Synopsis    [Select nodes visible in the mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkFpgaCollect( Seq_FpgaMan_t * p )
{
    Abc_Ntk_t * pNtk = p->pNtk;
    Abc_Obj_t * pObj;
    int i;
    Vec_PtrClear( p->vMapping );
    Vec_PtrClear( p->vMapCuts );
    Abc_NtkIncrementTravId( pNtk );
    Abc_NtkForEachPo( pNtk, pObj, i )
        Abc_NodeFpgaCollect_rec( p, Abc_ObjFanin0(pObj) );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


