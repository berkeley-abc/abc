/**CFile****************************************************************

  FileName    [seqRetIter.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Construction and manipulation of sequential AIGs.]

  Synopsis    [Iterative delay computation in FPGA mapping/retiming package.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: seqRetIter.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "seqInt.h"
#include "main.h"
#include "fpga.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static float Seq_NtkMappingSearch_rec( Abc_Ntk_t * pNtk, float FiMin, float FiMax, float Delta, int fVerbose );
static int   Seq_NtkMappingForPeriod( Abc_Ntk_t * pNtk, float Fi, int fVerbose );
static int   Seq_NtkNodeUpdateLValue( Abc_Obj_t * pObj, float Fi, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vDelays );
static void  Seq_NodeRetimeSetLag_rec( Abc_Obj_t * pNode, char Lag );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Computes the retiming lags for arbitrary network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Seq_NtkRetimeDelayLags( Abc_Ntk_t * pNtkOld, Abc_Ntk_t * pNtk, int fVerbose )
{
    Abc_Seq_t * p = pNtk->pManFunc;
    Abc_Obj_t * pNode;
    float FiMax, FiBest, Delta;
    int i, RetValue;
    char NodeLag;

    assert( Abc_NtkIsSeq( pNtk ) );

    // the root AND gates and node delay should be assigned
    assert( p->vMapAnds );
    assert( p->vMapCuts );
    assert( p->vMapDelays );

    // guess the upper bound on the clock period
    if ( Abc_NtkHasMapping(pNtkOld) )
    {
        // assign the accuracy for min-period computation
        Delta = Mio_LibraryReadDelayNand2Max(Abc_FrameReadLibGen());
        if ( Delta == 0.0 )
        {
            Delta = Mio_LibraryReadDelayAnd2Max(Abc_FrameReadLibGen());
            if ( Delta == 0.0 )
            {
                printf( "Cannot retime/map if the library does not have NAND2 or AND2.\n" );
                return;
            }
        }
        // get the upper bound on the clock period
        FiMax = Delta * (2 + Seq_NtkLevelMax(pNtk));
        Delta /= 2;
    }
    else
    {
        FiMax = (float)2.0 + Abc_NtkGetLevelNum(pNtkOld);
        Delta = 1;
    }

    // make sure this clock period is feasible
    assert( Seq_NtkMappingForPeriod( pNtk, FiMax, fVerbose ) );

    // search for the optimal clock period between 0 and nLevelMax
    FiBest = Seq_NtkMappingSearch_rec( pNtk, 0.0, FiMax, Delta, fVerbose );

    // recompute the best l-values
    RetValue = Seq_NtkMappingForPeriod( pNtk, FiBest, fVerbose );
    assert( RetValue );

    // write the retiming lags for both phases of each node
    Vec_StrFill( p->vLags,  p->nSize, 0 );
    Vec_PtrForEachEntry( p->vMapAnds, pNode, i )
    {
        NodeLag = Seq_NodeComputeLagFloat( Seq_NodeGetLValueP(pNode), FiBest );
//        Seq_NodeSetLag( pNode, NodeLag );
        Seq_NodeRetimeSetLag_rec( pNode, NodeLag );
    }

    // print the result
    if ( fVerbose )
        printf( "The best clock period is %6.2f.\n", FiBest );
}

/**Function*************************************************************

  Synopsis    [Performs binary search for the optimal clock period.]

  Description [Assumes that FiMin is infeasible while FiMax is feasible.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Seq_NtkMappingSearch_rec( Abc_Ntk_t * pNtk, float FiMin, float FiMax, float Delta, int fVerbose )
{
    float Median;
    assert( FiMin < FiMax );
    if ( FiMin + Delta >= FiMax )
        return FiMax;
    Median = FiMin + (FiMax - FiMin)/2;
    if ( Seq_NtkMappingForPeriod( pNtk, Median, fVerbose ) )
        return Seq_NtkMappingSearch_rec( pNtk, FiMin, Median, Delta, fVerbose ); // Median is feasible
    else 
        return Seq_NtkMappingSearch_rec( pNtk, Median, FiMax, Delta, fVerbose ); // Median is infeasible
}

/**Function*************************************************************

  Synopsis    [Returns 1 if retiming with this clock period is feasible.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Seq_NtkMappingForPeriod( Abc_Ntk_t * pNtk, float Fi, int fVerbose )
{
    Abc_Seq_t * p = pNtk->pManFunc;
    Vec_Ptr_t * vLeaves, * vDelays;
    Abc_Obj_t * pObj;
    int i, c, RetValue, fChange, Counter;
    char * pReason = "";

    // set l-values of all nodes to be minus infinity
    Vec_IntFill( p->vLValues,  p->nSize, -ABC_INFINITY );

    // set l-values of constants and PIs
    pObj = Abc_NtkObj( pNtk, 0 );
    Seq_NodeSetLValueP( pObj, 0.0 );
    Abc_NtkForEachPi( pNtk, pObj, i )
        Seq_NodeSetLValueP( pObj, 0.0 );

    // update all values iteratively
    Counter = 0;
    for ( c = 0; c < p->nMaxIters; c++ )
    {
        fChange = 0;
        Vec_PtrForEachEntry( p->vMapAnds, pObj, i )
        {
            Counter++;
            vLeaves = Vec_VecEntry( p->vMapCuts, i );
            vDelays = Vec_VecEntry( p->vMapDelays, i );
            RetValue = Seq_NtkNodeUpdateLValue( pObj, Fi, vLeaves, vDelays );
            if ( RetValue == SEQ_UPDATE_YES ) 
                fChange = 1;
        }
        Abc_NtkForEachPo( pNtk, pObj, i )
        {
            RetValue = Seq_NtkNodeUpdateLValue( pObj, Fi, NULL, NULL );
            if ( RetValue == SEQ_UPDATE_FAIL )
                break;
        }
        if ( RetValue == SEQ_UPDATE_FAIL )
            break;
        if ( fChange == 0 )
            break;
    }
    if ( c == p->nMaxIters )
    {
        RetValue = SEQ_UPDATE_FAIL;
        pReason = "(timeout)";
    }
    else
        c++;

    // report the results
    if ( fVerbose )
    {
        if ( RetValue == SEQ_UPDATE_FAIL )
            printf( "Period = %6.2f.  Iterations = %3d.  Updates = %10d.    Infeasible %s\n", Fi, c, Counter, pReason );
        else
            printf( "Period = %6.2f.  Iterations = %3d.  Updates = %10d.      Feasible\n",    Fi, c, Counter );
    }
    return RetValue != SEQ_UPDATE_FAIL;
}

/**Function*************************************************************

  Synopsis    [Computes the l-value of the node.]

  Description [The node can be internal or a PO.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Seq_NtkNodeUpdateLValue( Abc_Obj_t * pObj, float Fi, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vDelays )
{
    Abc_Seq_t * p = pObj->pNtk->pManFunc;
    float lValueOld, lValueNew, lValueCur, lValuePin;
    unsigned SeqEdge;
    Abc_Obj_t * pLeaf;
    int i;

    assert( !Abc_ObjIsPi(pObj) );
    assert( Abc_ObjFaninNum(pObj) > 0 );
    // consider the case of the PO
    if ( Abc_ObjIsPo(pObj) )
    {
        lValueCur = Seq_NodeGetLValueP(Abc_ObjFanin0(pObj)) - Fi * Seq_ObjFaninL0(pObj);
        return (lValueCur > Fi + p->fEpsilon)? SEQ_UPDATE_FAIL : SEQ_UPDATE_NO;
    }
    // get the new arrival time of the cut output
    lValueNew = -ABC_INFINITY;
    Vec_PtrForEachEntry( vLeaves, pLeaf, i )
    {
        SeqEdge   = (unsigned)pLeaf;
        pLeaf     = Abc_NtkObj( pObj->pNtk, SeqEdge >> 8 );
        lValueCur = Seq_NodeGetLValueP(pLeaf) - Fi * (SeqEdge & 255);
        lValuePin = Abc_Int2Float( (int)Vec_PtrEntry(vDelays, i) );
        if ( lValueNew < lValuePin + lValueCur )
            lValueNew = lValuePin + lValueCur;
    }
    // compare 
    lValueOld = Seq_NodeGetLValueP( pObj );
    if ( lValueNew <= lValueOld + p->fEpsilon )
        return SEQ_UPDATE_NO;
    // update the values
    if ( lValueNew > lValueOld + p->fEpsilon )
        Seq_NodeSetLValueP( pObj, lValueNew );
    return SEQ_UPDATE_YES;
}



/**Function*************************************************************

  Synopsis    [Add sequential edges.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Seq_NodeRetimeSetLag_rec( Abc_Obj_t * pNode, char Lag )
{
    if ( pNode->pCopy )
        return;
    Seq_NodeRetimeSetLag_rec( Abc_ObjFanin0(pNode), Lag );
    Seq_NodeRetimeSetLag_rec( Abc_ObjFanin1(pNode), Lag );
    Seq_NodeSetLag( pNode, Lag );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


