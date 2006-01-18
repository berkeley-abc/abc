/**CFile****************************************************************

  FileName    [fraigSim.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [And-Inverter Graph package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: fraigSim.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Simulates all nodes using the given simulation info.]

  Description [Returns the simulation info for all nodes.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManSimulateInfo( Aig_Man_t * p, Aig_SimInfo_t * pInfoPi, Aig_SimInfo_t * pInfoAll )
{
    Aig_Node_t * pNode;
    unsigned * pDataPi, * pDataPo, * pData0, * pData1, * pDataAnd;
    int i, k, fComp0, fComp1;

    assert( !pInfoPi->Type ); // PI siminfo
    // set the constant sim info
    pData1 = Aig_SimInfoForNode( pInfoAll, p->pConst1 );
    for ( k = 0; k < pInfoPi->nWords; k++ )
        pData1[k] = ~((unsigned)0);
    // set the PI siminfo
    Aig_ManForEachPi( p, pNode, i )
    {
        pDataPi  = Aig_SimInfoForPi( pInfoPi, i );
        pDataAnd = Aig_SimInfoForNode( pInfoAll, pNode );
        for ( k = 0; k < pInfoPi->nWords; k++ )
            pDataAnd[k] = pDataPi[k];
    }
    // simulate the nodes
    Aig_ManForEachAnd( p, pNode, i )
    {
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
    // derive the PO siminfo
    Aig_ManForEachPi( p, pNode, i )
    {
        pDataPo  = Aig_SimInfoForNode( pInfoAll, pNode );
        pDataAnd = Aig_SimInfoForNode( pInfoAll, Aig_NodeFanin0(pNode) );
        if ( Aig_NodeFaninC0(pNode) )
            for ( k = 0; k < pInfoPi->nWords; k++ )
                pDataPo[k] = ~pDataAnd[k];
        else
            for ( k = 0; k < pInfoPi->nWords; k++ )
                pDataPo[k] = pDataAnd[k];
    }
}



/**Function*************************************************************

  Synopsis    [Allocates the simulation info.]

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

  Synopsis    [Sets the simulation info to zero.]

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

  Synopsis    [Sets the random simulation info.]

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

  Synopsis    [Sets the random simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_SimInfoFromPattern( Aig_SimInfo_t * p, Aig_Pattern_t * pPat )
{
    unsigned * pData;
    int i, k;
    assert( p->Type == 0 );
    assert( p->nNodes == pPat->nBits );
    for ( i = 0; i < p->nNodes; i++ )
    {
        // get the pointer to the bitdata for node i
        pData = p->pData + p->nWords * i;
        // fill in the bit data according to the pattern
        if ( Aig_InfoHasBit(pPat->pData, i) ) // PI has bit set to 1
            for ( k = 0; k < p->nWords; k++ )
                pData[k] = ~((unsigned)0);
        else
            for ( k = 0; k < p->nWords; k++ )
                pData[k] = 0;
        // flip one bit
        Aig_InfoXorBit( pData, i );
    }
}

/**Function*************************************************************

  Synopsis    [Resizes the simulation info.]

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
    p->nWords   *= 2;
    p->nPatsMax *= 2;
    free( p->pData );
    p->pData = pData;
}

/**Function*************************************************************

  Synopsis    [Deallocates the simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_SimInfoFree( Aig_SimInfo_t * p )
{
    free( p->pData );
    free( p );
}


/**Function*************************************************************

  Synopsis    [Allocates the simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Pattern_t * Aig_PatternAlloc( int nBits )
{
    Aig_Pattern_t * pPat;
    pPat = ALLOC( Aig_Pattern_t, 1 );
    memset( pPat, 0, sizeof(Aig_Pattern_t) );
    pPat->nBits  = nBits;
    pPat->nWords = Aig_BitWordNum(nBits);
    pPat->pData  = ALLOC( unsigned, pPat->nWords );
    return pPat;
}

/**Function*************************************************************

  Synopsis    [Cleans the pattern.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_PatternClean( Aig_Pattern_t * pPat )
{
    memset( pPat->pData, 0, sizeof(unsigned) * pPat->nWords );
}

/**Function*************************************************************

  Synopsis    [Sets the random pattern.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_PatternRandom( Aig_Pattern_t * pPat )
{
    int i;
    for ( i = 0; i < pPat->nWords; i++ )
        pPat->pData[i] = ((((unsigned)rand()) << 24) ^ (((unsigned)rand()) << 12) ^ ((unsigned)rand()));
}

/**Function*************************************************************

  Synopsis    [Deallocates the pattern.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_PatternFree( Aig_Pattern_t * pPat )
{
    free( pPat->pData );
    free( pPat );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


