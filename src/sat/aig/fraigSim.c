/**CFile****************************************************************

  FileName    [aigSim.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: aigSim.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Simulates all nodes using random simulation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManSimulateRandomFirst( Aig_Man_t * p )
{
    Aig_SimInfo_t * pInfoPi, * pInfoAll;
    assert( p->pInfo && p->pInfoTemp );
    // create random PI info
    pInfoPi = Aig_SimInfoAlloc( p->vPis->nSize, Aig_BitWordNum(p->pParam->nPatsRand), 0 );
    Aig_SimInfoRandom( pInfoPi );
    // simulate it though the circuit
    pInfoAll = Aig_ManSimulateInfo( p, pInfoPi );
    // detect classes
    p->vClasses = Aig_ManDeriveClassesFirst( p, pInfoAll );
    Aig_SimInfoFree( pInfoAll );
    // save simulation info
    p->pInfo = pInfoPi;
    p->pInfoTemp = Aig_SimInfoAlloc( p->vNodes->nSize, Aig_BitWordNum(p->vPis->nSize), 1 );
}

/**Function*************************************************************

  Synopsis    [Simulates all nodes using the given simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_SimInfo_t * Aig_ManSimulateInfo( Aig_Man_t * p, Aig_SimInfo_t * pInfoPi )
{
    Aig_SimInfo_t * pInfoAll;
    Aig_Node_t * pNode;
    unsigned * pDataPi, * pData0, * pData1, * pDataAnd;
    int i, k, fComp0, fComp1;

    assert( !pInfoPi->Type ); // PI siminfo
    // allocate sim info for all nodes
    pInfoAll = Aig_SimInfoAlloc( p->vNodes->nSize, pInfoPi->nWords, 1 );
    // set the constant sim info
    pData1 = Aig_SimInfoForNode( pInfoAll, p->pConst1 );
    for ( k = 0; k < pInfoPi->nWords; k++ )
        pData1[k] = ~((unsigned)0);
    // copy the PI siminfo
    Vec_PtrForEachEntry( p->vPis, pNode, i )
    {
        pDataPi  = Aig_SimInfoForPi( pInfoPi, i );
        pDataAnd = Aig_SimInfoForNode( pInfoAll, pNode );
        for ( k = 0; k < pInfoPi->nWords; k++ )
            pDataAnd[k] = pDataPi[k];
    }
    // simulate the nodes
    Vec_PtrForEachEntry( p->vNodes, pNode, i )
    {
        if ( !Aig_NodeIsAnd(pNode) )
            continue;
        pData0   = Aig_SimInfoForNode( pInfoAll, Aig_NodeFanin0(pNode) );
        pData1   = Aig_SimInfoForNode( pInfoAll, Aig_NodeFanin1(pNode) );
        pDataAnd = Aig_SimInfoForNode( pInfoAll, pNode                 );
        fComp0 = Aig_NodeFaninC0(pNode);
        fComp1 = Aig_NodeFaninC1(pNode);
        if ( fComp0 && fComp1 )
            for ( k = 0; k < pInfoPi->nWords; k++ )
                pDataAnd[k] = ~pData0[k] & ~pData1[k];
        else if ( fComp0  )
            for ( k = 0; k < pInfoPi->nWords; k++ )
                pDataAnd[k] = ~pData0[k] &  pData1[k];
        else if ( fComp1 )
            for ( k = 0; k < pInfoPi->nWords; k++ )
                pDataAnd[k] =  pData0[k] & ~pData1[k];
        else 
            for ( k = 0; k < pInfoPi->nWords; k++ )
                pDataAnd[k] =  pData0[k] &  pData1[k];
    }
    return pInfoAll;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_SimInfo_t * Aig_SimInfoAlloc( int nNodes, int nWords, int Type )
{
    Aig_SimInfo_t * p;
    p = ALLOC( Aig_SimInfo_t, 1 );
    memset( p, 0, sizeof(Aig_SimInfo_t) );
    p->Type     = Type;
    p->nNodes   = nNodes;
    p->nWords   = nWords;
    p->nPatsMax = nWords * sizeof(unsigned) * 8;
    p->pData    = ALLOC( unsigned, nNodes * nWords );
    return p;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_SimInfoClean( Aig_SimInfo_t * p )
{
    int i, Size = p->nNodes * p->nWords;
    p->nPatsCur = 0;
    for ( i = 0; i < Size; i++ )
        p->pData[i] = 0;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_SimInfoRandom( Aig_SimInfo_t * p )
{
    int i, Size = p->nNodes * p->nWords;
    unsigned * pData;
    for ( i = 0; i < Size; i++ )
        p->pData[i] = ((((unsigned)rand()) << 24) ^ (((unsigned)rand()) << 12) ^ ((unsigned)rand()));
    // make sure the first bit of all nodes is 0
    for ( i = 0; i < p->nNodes; i++ )
    {
        pData = p->pData + p->nWords * i;
        *pData <<= 1;
    }
    p->nPatsCur = p->nPatsMax;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_SimInfoResize( Aig_SimInfo_t * p )
{
    unsigned * pData;
    int i, k;
    assert( p->nPatsCur == p->nPatsMax );
    pData = ALLOC( unsigned, 2 * p->nNodes * p->nWords );
    for ( i = 0; i < p->nNodes; i++ )
    {
        for ( k = 0; k < p->nWords; k++ )
            pData[2 * p->nWords * i + k] = p->pData[p->nWords * i + k];
        for ( k = 0; k < p->nWords; k++ )
            pData[2 * p->nWords * i + k + p->nWords] = 0;
    }
    p->nPatsMax *= 2;
    p->nWords   *= 2;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_SimInfoFree( Aig_SimInfo_t * p )
{
    free( p->pData );
    free( p );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


