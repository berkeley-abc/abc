/**CFile****************************************************************

  FileName    [simSymSim.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Simulation to determine two-variable symmetries.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: simSymSim.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "sim.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static void Sim_SymmsCreateSquare( Sym_Man_t * p, unsigned * pPat );
static void Sim_SymmsDeriveInfo( Sym_Man_t * p, unsigned * pPat, Abc_Obj_t * pNode, Extra_BitMat_t * pMatrix, int Output );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Detects non-symmetric pairs using one pattern.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sim_SymmsSimulate( Sym_Man_t * p, unsigned * pPat, Vec_Ptr_t * vMatrsNonSym )
{
    Abc_Obj_t * pNode;
    int i;
    // create the simulation matrix
    Sim_SymmsCreateSquare( p, pPat );
    // simulate each node in the DFS order
    Vec_PtrForEachEntry( p->vNodes, pNode, i )
    {
        if ( Abc_NodeIsConst(pNode) )
            continue;
        Sim_UtilSimulateNodeOne( pNode, p->vSim, p->nSimWords );
    }
    // collect info into the CO matrices
    Abc_NtkForEachCo( p->pNtk, pNode, i )
    {
        pNode = Abc_ObjFanin0(pNode);
        if ( Abc_ObjIsCi(pNode) || Abc_NodeIsConst(pNode) )
            continue;
        if ( Vec_IntEntry(p->vPairsTotal,i) == Vec_IntEntry(p->vPairsSym,i) + Vec_IntEntry(p->vPairsNonSym,i) )
            continue;
        Sim_SymmsDeriveInfo( p, pPat, pNode, Vec_PtrEntry(vMatrsNonSym, i), i );
    }
}

/**Function*************************************************************

  Synopsis    [Creates the square matrix of simulation info.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sim_SymmsCreateSquare( Sym_Man_t * p, unsigned * pPat )
{
    unsigned * pSimInfo;
    Abc_Obj_t * pNode;
    int i, w;
    // for each PI var copy the pattern
    Abc_NtkForEachCi( p->pNtk, pNode, i )
    {
        pSimInfo = Vec_PtrEntry( p->vSim, pNode->Id );
        if ( Sim_HasBit(pPat, i) )
        {
            for ( w = 0; w < p->nSimWords; w++ )
                pSimInfo[w] = SIM_MASK_FULL;
        }
        else
        {
            for ( w = 0; w < p->nSimWords; w++ )
                pSimInfo[w] = 0;
        }
        // flip one bit
        Sim_XorBit( pSimInfo, i );
    }
}

/**Function*************************************************************

  Synopsis    [Transfers the info to the POs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sim_SymmsDeriveInfo( Sym_Man_t * p, unsigned * pPat, Abc_Obj_t * pNode, Extra_BitMat_t * pMat, int Output )
{
    unsigned * pSuppInfo;
    unsigned * pSimInfo;
    int i, w;
    // get the simuation info for the node
    pSimInfo = Vec_PtrEntry( p->vSim, pNode->Id );
    pSuppInfo = Vec_PtrEntry( p->vSuppFun, Output );
    // generate vectors A1 and A2
    for ( w = 0; w < p->nSimWords; w++ )
    {
        p->uPatCol[w] = pSuppInfo[w] & pPat[w] &  pSimInfo[w];
        p->uPatRow[w] = pSuppInfo[w] & pPat[w] & ~pSimInfo[w];
    }
    // add two dimensions
    for ( i = 0; i < p->nInputs; i++ )
        if ( Sim_HasBit( p->uPatCol, i ) )
            Extra_BitMatrixOr( pMat, i, p->uPatRow );
    // add two dimensions
    for ( i = 0; i < p->nInputs; i++ )
        if ( Sim_HasBit( p->uPatRow, i ) )
            Extra_BitMatrixOr( pMat, i, p->uPatCol );
    // generate vectors B1 and B2
    for ( w = 0; w < p->nSimWords; w++ )
    {
        p->uPatCol[w] = pSuppInfo[w] & ~pPat[w] &  pSimInfo[w];
        p->uPatRow[w] = pSuppInfo[w] & ~pPat[w] & ~pSimInfo[w];
    }
    // add two dimensions
    for ( i = 0; i < p->nInputs; i++ )
        if ( Sim_HasBit( p->uPatCol, i ) )
            Extra_BitMatrixOr( pMat, i, p->uPatRow );
    // add two dimensions
    for ( i = 0; i < p->nInputs; i++ )
        if ( Sim_HasBit( p->uPatRow, i ) )
            Extra_BitMatrixOr( pMat, i, p->uPatCol );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


