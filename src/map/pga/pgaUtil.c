/**CFile****************************************************************

  FileName    [pgaUtil.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [FPGA mapper.]

  Synopsis    [Verious utilities.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: pgaUtil.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "pgaInt.h"

#define PGA_CO_LIST_SIZE  5

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns the results of mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Pga_MappingResults( Pga_Man_t * p )
{
    Vec_Ptr_t * vResult;
    Pga_Node_t * pNode;
    int i;
    vResult = Vec_PtrAlloc( 1000 );
    Pga_ManForEachObjDirect( p, pNode, i )
    {
        // skip the CIs and nodes not used in the mapping
        if ( !pNode->Match.pCut || !pNode->nRefs )
            continue;
        pNode->Match.pCut->uSign = pNode->Id;
        Vec_PtrPush( vResult, pNode->Match.pCut );
    }
    return vResult;
}

/**Function*************************************************************

  Synopsis    [Computes the maximum arrival times.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Pga_TimeComputeArrivalMax( Pga_Man_t * p )
{
    Pga_Node_t * pNode;
    float ArrivalMax;
    int i;
    ArrivalMax = -ABC_INFINITY;
    Pga_ManForEachCoDriver( p, pNode, i )
        ArrivalMax = ABC_MAX( ArrivalMax, pNode->Match.Delay );
    return ArrivalMax;
}


/**Function*************************************************************

  Synopsis    [Computes required times of all nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pga_MappingComputeRequired( Pga_Man_t * p )
{
    Pga_Node_t * pNode, * pFanin;
    Cut_Cut_t * pCutBest;
    float RequiredNew;
    int i, k;
    // clean the required times of all nodes
    Pga_ManForEachObjDirect( p, pNode, i )
        pNode->Required = ABC_INFINITY;
    // get the global required times
    p->AreaGlobal     = Pga_TimeComputeArrivalMax( p );
    p->RequiredGlobal = ABC_MAX( p->AreaGlobal, p->RequiredUser );
    // set the global required times of the CO drivers
    Pga_ManForEachCoDriver( p, pNode, i )
        pNode->Required = p->RequiredGlobal;
    // propagate the required times in the reverse topological order
    Pga_ManForEachObjReverse( p, pNode, i )
    {
        // skip the CIs and nodes not used in the mapping
        if ( !pNode->Match.pCut || !pNode->nRefs )
            continue;
        // get the required time for children
        pCutBest    = pNode->Match.pCut;
        RequiredNew = pNode->Required - p->pLutDelays[pCutBest->nLeaves];
        // update the required time of the children
        for ( k = 0; k < (int)pCutBest->nLeaves; k++ )
        {
            pFanin = Pga_Node( p, pCutBest->pLeaves[k] );
            pFanin->Required = ABC_MIN( pFanin->Required, RequiredNew );
        }
    }
    // check that the required times does not contradict the arrival times
    Pga_ManForEachObjDirect( p, pNode, i )
        assert( !pNode->Match.pCut || pNode->Match.Delay < pNode->Required + p->Epsilon );

}

/**Function*************************************************************

  Synopsis    [Sets references and computes area for the current mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Pga_MappingSetRefsAndArea( Pga_Man_t * p )
{
    Pga_Node_t * pNode, * pFanin;
    Cut_Cut_t * pCutBest;
    float AreaTotal;
    int i, k;
    // clean all the references
    Pga_ManForEachObjDirect( p, pNode, i )
        pNode->nRefs = 0;
    // set the references of the CO drivers
    Pga_ManForEachCoDriver( p, pNode, i )
        pNode->nRefs++;
    // go through the nodes in the reverse order
    AreaTotal = 0.0;
    Pga_ManForEachObjReverse( p, pNode, i )
    {
        // skip the CIs and nodes not used in the mapping
        if ( !pNode->Match.pCut || !pNode->nRefs )
            continue;
        // increate the reference count of the children
        pCutBest   = pNode->Match.pCut;
        AreaTotal += p->pLutAreas[pCutBest->nLeaves];
        // update the required time of the children
        for ( k = 0; k < (int)pCutBest->nLeaves; k++ )
        {
            pFanin = Pga_Node( p, pCutBest->pLeaves[k] );
            pFanin->nRefs++;
        }
    }
    return AreaTotal;
}

/**Function*************************************************************

  Synopsis    [Computes switching activity of the mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
float Pga_MappingGetSwitching( Pga_Man_t * p )
{
    float Switching;
    Pga_Node_t * pNode;
    int i;
    Switching = 0;
    Pga_ManForEachObjDirect( p, pNode, i )
    {
        // skip the CIs and nodes not used in the mapping
        if ( !pNode->Match.pCut || !pNode->nRefs )
            continue;
        Switching += pNode->Switching;
    }
    return Switching;
}

/**Function*************************************************************

  Synopsis    [Compares the outputs by their arrival times.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Pga_MappingCompareOutputDelay( Pga_Node_t ** ppNode1, Pga_Node_t ** ppNode2 )
{
    Pga_Node_t * pNode1 = *ppNode1;
    Pga_Node_t * pNode2 = *ppNode2;
    float Arrival1 = pNode1->Match.Delay;
    float Arrival2 = pNode2->Match.Delay;
    if ( Arrival1 < Arrival2 )
        return -1;
    if ( Arrival1 > Arrival2 )
        return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Finds given number of latest arriving COs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pga_MappingFindLatest( Pga_Man_t * p, int * pNodes, int nNodesMax )
{
    Pga_Node_t * pNodeI, * pNodeK;
    Abc_Obj_t * pObjCo;
    int nNodes, i, k, v;
    assert( Abc_NtkCoNum(p->pParams->pNtk) >= nNodesMax );
    pNodes[0] = 0;
    nNodes = 1;
//    for ( i = 1; i < p->nOutputs; i++ )
    Pga_ManForEachCoDriver( p, pNodeI, i )
    {
        for ( k = nNodes - 1; k >= 0; k-- )
        {
            pObjCo = Abc_NtkCo( p->pParams->pNtk, pNodes[k] );
            pNodeK = Pga_Node( p, Abc_ObjFaninId0(pObjCo) );
            if ( Pga_MappingCompareOutputDelay( &pNodeK, &pNodeI ) >= 0 )
                break;
        }
        if ( k == nNodesMax - 1 )
            continue;
        if ( nNodes < nNodesMax )
            nNodes++;
        for ( v = nNodes - 1; v > k+1; v-- )
            pNodes[v] = pNodes[v-1];
        pNodes[k+1] = i;
    }
}

/**Function*************************************************************

  Synopsis    [Prints a bunch of latest arriving outputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Pga_MappingPrintOutputArrivals( Pga_Man_t * p )
{
    int pSorted[PGA_CO_LIST_SIZE];
    Abc_Ntk_t * pNtk = p->pParams->pNtk;
    Abc_Obj_t * pObjCo;
    Pga_Node_t * pNode;
    int Limit, MaxNameSize, i;

    // determine the number of nodes to print
    Limit = (Abc_NtkCoNum(pNtk) < PGA_CO_LIST_SIZE)? Abc_NtkCoNum(pNtk) : PGA_CO_LIST_SIZE;

    // determine the order
    Pga_MappingFindLatest( p, pSorted, Limit );

    // determine max size of the node's name
    MaxNameSize = 0;
    for ( i = 0; i < Limit; i++ )
    {
        pObjCo = Abc_NtkCo( pNtk, pSorted[i] );
        if ( MaxNameSize < (int)strlen( Abc_ObjName(pObjCo) ) )
            MaxNameSize = strlen( Abc_ObjName(pObjCo) );
    }

    // print the latest outputs
    for ( i = 0; i < Limit; i++ )
    {
        // get the i-th latest output
        pObjCo = Abc_NtkCo( pNtk, pSorted[i] );
        pNode  = Pga_Node( p, pObjCo->Id );
        // print out the best arrival time
        printf( "Output  %-*s : ", MaxNameSize + 3, Abc_ObjName(pObjCo) );
        printf( "Delay = %8.2f  ", (double)pNode->Match.Delay );
        if ( Abc_ObjFaninC0(pObjCo) )
            printf( "NEG" );
        else
            printf( "POS" );
        printf( "\n" );
    }
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


