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

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// storing arrival times in the nodes
static inline int  Abc_NodeReadLValue( Abc_Obj_t * pNode )            { return Vec_IntEntry( (pNode)->pNtk->pData, (pNode)->Id );        }
static inline void Abc_NodeSetLValue( Abc_Obj_t * pNode, int Value )  { Vec_IntWriteEntry( (pNode)->pNtk->pData, (pNode)->Id, (Value) ); }

// the internal procedures
static int Abc_NtkRetimeSearch_rec( Abc_Ntk_t * pNtk, int FiMin, int FiMax );
static int Abc_NtkRetimeForPeriod( Abc_Ntk_t * pNtk, int Fi );
static int Abc_NodeUpdateLValue( Abc_Obj_t * pObj, int Fi );

// node status after updating its arrival time
enum { ABC_UPDATE_FAIL, ABC_UPDATE_NO, ABC_UPDATE_YES };

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Retimes AIG for optimal delay.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkSeqRetimeDelay( Abc_Ntk_t * pNtk )
{
    int FiMax, FiBest;
    assert( Abc_NtkIsSeq( pNtk ) );

    // start storage for sequential arrival times
    assert( pNtk->pData == NULL );
    pNtk->pData = Vec_IntAlloc( 0 );

    // get the maximum possible clock
    FiMax = Abc_NtkNodeNum(pNtk);

    // make sure this clock period is feasible
    assert( Abc_NtkRetimeForPeriod( pNtk, FiMax ) );

    // search for the optimal clock period between 0 and nLevelMax
    FiBest = Abc_NtkRetimeSearch_rec( pNtk, 0, FiMax );
    // print the result
    printf( "The best clock period is %3d.\n", FiBest );

    // free storage
    Vec_IntFree( pNtk->pData );
    pNtk->pData = NULL;
}

/**Function*************************************************************

  Synopsis    [Performs binary search for the optimal clock period.]

  Description [Assumes that FiMin is infeasible while FiMax is feasible.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRetimeSearch_rec( Abc_Ntk_t * pNtk, int FiMin, int FiMax )
{
    int Median;

    assert( FiMin < FiMax );
    if ( FiMin + 1 == FiMax )
        return FiMax;

    Median = FiMin + (FiMax - FiMin)/2;

    if ( Abc_NtkRetimeForPeriod( pNtk, Median ) )
        return Abc_NtkRetimeSearch_rec( pNtk, FiMin, Median ); // Median is feasible
    else 
        return Abc_NtkRetimeSearch_rec( pNtk, Median, FiMax ); // Median is infeasible
}

/**Function*************************************************************

  Synopsis    [Returns 1 if retiming with this clock period is feasible.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRetimeForPeriod( Abc_Ntk_t * pNtk, int Fi )
{
    Vec_Ptr_t * vFrontier;
    Abc_Obj_t * pObj, * pFanout;
    int RetValue, i, k;

    // set l-values of all nodes to be minus infinity
    Vec_IntFill( pNtk->pData, Abc_NtkObjNumMax(pNtk), -ABC_INFINITY );

    // start the frontier by including PI fanouts
    vFrontier = Vec_PtrAlloc( 100 );
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
    Vec_PtrForEachEntry( vFrontier, pObj, i )
    {
        RetValue = Abc_NodeUpdateLValue( pObj, Fi );
        if ( RetValue == ABC_UPDATE_FAIL )
            break;
        // unmark the node as processed
        pObj->fMarkA = 0;
        if ( RetValue == ABC_UPDATE_NO ) 
            continue;
        assert( RetValue == ABC_UPDATE_YES );
        // arrival times have changed - add fanouts to the frontier
        Abc_ObjForEachFanout( pObj, pFanout, k )
            if ( pFanout->fMarkA == 0 )
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
        printf( "Period = %3d.  Updated nodes = %6d.    Infeasible\n", Fi, vFrontier->nSize );
    else
        printf( "Period = %3d.  Updated nodes = %6d.    Feasible\n",   Fi, vFrontier->nSize );
    Vec_PtrFree( vFrontier );
    return RetValue != ABC_UPDATE_FAIL;
}

/**Function*************************************************************

  Synopsis    [Computes the l-value of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeUpdateLValue( Abc_Obj_t * pObj, int Fi )
{
    int lValueNew, lValue0, lValue1;
    assert( !Abc_ObjIsPi(pObj) );
    lValue0 = Abc_NodeReadLValue(Abc_ObjFanin0(pObj)) - Fi * Abc_ObjFaninL0(pObj);
    if ( Abc_ObjFaninNum(pObj) == 2 )
        lValue1 = Abc_NodeReadLValue(Abc_ObjFanin1(pObj)) - Fi * Abc_ObjFaninL1(pObj);
    else
        lValue1 = -ABC_INFINITY;
    lValueNew = 1 + ABC_MAX( lValue0, lValue1 );
    if ( Abc_ObjIsPo(pObj) && lValueNew > Fi )
        return ABC_UPDATE_FAIL;
    if ( lValueNew == Abc_NodeReadLValue(pObj) )
        return ABC_UPDATE_NO;
    Abc_NodeSetLValue( pObj, lValueNew );
    return ABC_UPDATE_YES;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

