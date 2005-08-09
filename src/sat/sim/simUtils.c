/**CFile****************************************************************

  FileName    [simUtils.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Various simulation utilities.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: simUtils.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "sim.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
 
////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Allocates simulation information for all nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Sim_UtilInfoAlloc( int nSize, int nWords, bool fClean )
{
    Vec_Ptr_t * vInfo;
    int i;
    vInfo = Vec_PtrAlloc( nSize );
    vInfo->pArray[0] = ALLOC( unsigned, nSize * nWords );
    if ( fClean )
        memset( vInfo->pArray[0], 0, sizeof(unsigned) * nSize * nWords );
    for ( i = 1; i < nSize; i++ )
        vInfo->pArray[i] = ((unsigned *)vInfo->pArray[i-1]) + nWords;
    vInfo->nSize = nSize;
    return vInfo;
}

/**Function*************************************************************

  Synopsis    [Allocates simulation information for all nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sim_UtilInfoFree( Vec_Ptr_t * p )
{
    free( p->pArray[0] );
    Vec_PtrFree( p );
}

/**Function*************************************************************

  Synopsis    [Adds the second supp-info the first.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sim_UtilInfoAdd( unsigned * pInfo1, unsigned * pInfo2, int nWords )
{
    int w;
    for ( w = 0; w < nWords; w++ )
        pInfo1[w] |= pInfo2[w];
}

/**Function*************************************************************

  Synopsis    [Returns the positions where pInfo2 is 1 while pInfo1 is 0.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sim_UtilInfoDetectDiffs( unsigned * pInfo1, unsigned * pInfo2, int nWords, Vec_Int_t * vDiffs )
{
    int w, b;
    unsigned uMask;
    vDiffs->nSize = 0;
    for ( w = 0; w < nWords; w++ )
        if ( uMask = (pInfo2[w] ^ pInfo1[w]) )
            for ( b = 0; b < 32; b++ )
                if ( uMask & (1 << b) )
                    Vec_IntPush( vDiffs, 32*w + b );
}

/**Function*************************************************************

  Synopsis    [Returns the positions where pInfo2 is 1 while pInfo1 is 0.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sim_UtilInfoDetectNews( unsigned * pInfo1, unsigned * pInfo2, int nWords, Vec_Int_t * vDiffs )
{
    int w, b;
    unsigned uMask;
    vDiffs->nSize = 0;
    for ( w = 0; w < nWords; w++ )
        if ( uMask = (pInfo2[w] & ~pInfo1[w]) )
            for ( b = 0; b < 32; b++ )
                if ( uMask & (1 << b) )
                    Vec_IntPush( vDiffs, 32*w + b );
}

/**Function*************************************************************

  Synopsis    [Computes structural supports.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sim_UtilComputeStrSupp( Sim_Man_t * p )
{
    Abc_Obj_t * pNode;
    unsigned * pSimmNode, * pSimmNode1, * pSimmNode2;
    int i, k;
    // assign the structural support to the PIs
    Abc_NtkForEachCi( p->pNtk, pNode, i )
        Sim_SuppStrSetVar( p, pNode, i );
    // derive the structural supports of the internal nodes
    Abc_NtkForEachNode( p->pNtk, pNode, i )
    {
        if ( Abc_NodeIsConst(pNode) )
            continue;
        pSimmNode  = p->vSuppStr->pArray[ pNode->Id ];
        pSimmNode1 = p->vSuppStr->pArray[ Abc_ObjFaninId0(pNode) ];
        pSimmNode2 = p->vSuppStr->pArray[ Abc_ObjFaninId1(pNode) ];
        for ( k = 0; k < p->nSuppWords; k++ )
            pSimmNode[k] = pSimmNode1[k] | pSimmNode2[k];
    }
    // set the structural supports of the PO nodes
    Abc_NtkForEachCo( p->pNtk, pNode, i )
    {
        pSimmNode  = p->vSuppStr->pArray[ pNode->Id ];
        pSimmNode1 = p->vSuppStr->pArray[ Abc_ObjFaninId0(pNode) ];
        for ( k = 0; k < p->nSuppWords; k++ )
            pSimmNode[k] = pSimmNode1[k];
    }
}

/**Function*************************************************************

  Synopsis    [Assigns random simulation info to the PIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sim_UtilAssignRandom( Sim_Man_t * p )
{
    Abc_Obj_t * pNode;
    unsigned * pSimInfo;
    int i, k;
    // assign the random/systematic simulation info to the PIs
    Abc_NtkForEachCi( p->pNtk, pNode, i )
    {
        pSimInfo = p->vSim0->pArray[pNode->Id];
        for ( k = 0; k < p->nSimWords; k++ )
            pSimInfo[k] = SIM_RANDOM_UNSIGNED;
    }
}

/**Function*************************************************************

  Synopsis    [Flips the simulation info of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sim_UtilFlipSimInfo( Sim_Man_t * p, Abc_Obj_t * pNode )
{
    unsigned * pSimInfo1, * pSimInfo2;
    int k;
    pSimInfo1 = p->vSim1->pArray[pNode->Id];
    pSimInfo2 = p->vSim0->pArray[pNode->Id];
    for ( k = 0; k < p->nSimWords; k++ )
        pSimInfo2[k] = ~pSimInfo1[k];
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the simulation infos are equal.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Sim_UtilCompareSimInfo( Sim_Man_t * p, Abc_Obj_t * pNode )
{
    unsigned * pSimInfo1, * pSimInfo2;
    int k;
    pSimInfo1 = p->vSim1->pArray[pNode->Id];
    pSimInfo2 = p->vSim0->pArray[pNode->Id];
    for ( k = 0; k < p->nSimWords; k++ )
        if ( pSimInfo2[k] != pSimInfo1[k] )
            return 0;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Simulates the internal nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sim_UtilSimulate( Sim_Man_t * p, bool fType )
{
    Abc_Obj_t * pNode;
    int i;
    // simulate the internal nodes
    Abc_NtkForEachNode( p->pNtk, pNode, i )
        Sim_UtilSimulateNode( p, pNode, fType, fType, fType );
    // assign simulation info of the CO nodes
    Abc_NtkForEachCo( p->pNtk, pNode, i )
        Sim_UtilSimulateNode( p, pNode, fType, fType, fType );
}

/**Function*************************************************************

  Synopsis    [Simulates one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sim_UtilSimulateNode( Sim_Man_t * p, Abc_Obj_t * pNode, bool fType, bool fType1, bool fType2 )
{
    unsigned * pSimmNode, * pSimmNode1, * pSimmNode2;
    int k, fComp1, fComp2;
    // simulate the internal nodes
    if ( Abc_ObjIsNode(pNode) )
    {
        if ( Abc_NodeIsConst(pNode) )
            return;

        if ( fType )
            pSimmNode  = p->vSim1->pArray[ pNode->Id ];
        else
            pSimmNode  = p->vSim0->pArray[ pNode->Id ];

        if ( fType1 )
            pSimmNode1 = p->vSim1->pArray[ Abc_ObjFaninId0(pNode) ];
        else
            pSimmNode1 = p->vSim0->pArray[ Abc_ObjFaninId0(pNode) ];

        if ( fType2 )
            pSimmNode2 = p->vSim1->pArray[ Abc_ObjFaninId1(pNode) ];
        else
            pSimmNode2 = p->vSim0->pArray[ Abc_ObjFaninId1(pNode) ];

        fComp1 = Abc_ObjFaninC0(pNode);
        fComp2 = Abc_ObjFaninC1(pNode);
        if ( fComp1 && fComp2 )
            for ( k = 0; k < p->nSimWords; k++ )
                pSimmNode[k] = ~pSimmNode1[k] & ~pSimmNode2[k];
        else if ( fComp1 && !fComp2 )
            for ( k = 0; k < p->nSimWords; k++ )
                pSimmNode[k] = ~pSimmNode1[k] &  pSimmNode2[k];
        else if ( !fComp1 && fComp2 )
            for ( k = 0; k < p->nSimWords; k++ )
                pSimmNode[k] =  pSimmNode1[k] & ~pSimmNode2[k];
        else // if ( fComp1 && fComp2 )
            for ( k = 0; k < p->nSimWords; k++ )
                pSimmNode[k] =  pSimmNode1[k] &  pSimmNode2[k];
    }
    else 
    {
        assert( Abc_ObjFaninNum(pNode) == 1 );
        if ( fType )
            pSimmNode  = p->vSim1->pArray[ pNode->Id ];
        else
            pSimmNode  = p->vSim0->pArray[ pNode->Id ];

        if ( fType1 )
            pSimmNode1 = p->vSim1->pArray[ Abc_ObjFaninId0(pNode) ];
        else
            pSimmNode1 = p->vSim0->pArray[ Abc_ObjFaninId0(pNode) ];

        fComp1 = Abc_ObjFaninC0(pNode);
        if ( fComp1 )
            for ( k = 0; k < p->nSimWords; k++ )
                pSimmNode[k] = ~pSimmNode1[k];
        else 
            for ( k = 0; k < p->nSimWords; k++ )
                pSimmNode[k] =  pSimmNode1[k];
    }
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the simulation infos are equal.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Sim_UtilCountSuppSizes( Sim_Man_t * p, int fStruct )
{
    Abc_Obj_t * pNode, * pNodeCi;
    int i, v, Counter;
    Counter = 0;
    if ( fStruct )
    {
        Abc_NtkForEachCo( p->pNtk, pNode, i )
            Abc_NtkForEachCi( p->pNtk, pNodeCi, v )
                Counter += Sim_SuppStrHasVar( p, pNode, v );
    }
    else
    {
        Abc_NtkForEachCo( p->pNtk, pNode, i )
            Abc_NtkForEachCi( p->pNtk, pNodeCi, v )
                Counter += Sim_SuppFunHasVar( p, i, v );
    }
    return Counter;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


