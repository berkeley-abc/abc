/**CFile****************************************************************

  FileName    [abcRenode.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcRenode.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "reo.h"
#include "if.h"
#include "kit.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int Abc_NtkRenodeEvalBdd( If_Cut_t * pCut );
static int Abc_NtkRenodeEvalSop( If_Cut_t * pCut );
static int Abc_NtkRenodeEvalAig( If_Cut_t * pCut );

static reo_man * s_pReo      = NULL;
static DdManager * s_pDd     = NULL;
static Vec_Int_t * s_vMemory = NULL;

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs renoding as technology mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkRenode( Abc_Ntk_t * pNtk, int nFaninMax, int nCubeMax, int fArea, int fUseBdds, int fUseSops, int fVerbose )
{
    extern Abc_Ntk_t * Abc_NtkIf( Abc_Ntk_t * pNtk, If_Par_t * pPars );
    If_Par_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtkNew;

    // set defaults
    memset( pPars, 0, sizeof(If_Par_t) );
    // user-controlable paramters
    pPars->nLutSize    =  nFaninMax;
    pPars->nCutsMax    =  nCubeMax;
    pPars->DelayTarget = -1;
    pPars->fPreprocess =  1;
    pPars->fArea       =  fArea;
    pPars->fFancy      =  0;
    pPars->fExpRed     =  0; //
    pPars->fLatchPaths =  0;
    pPars->fSeq        =  0;
    pPars->fVerbose    =  fVerbose;
    // internal parameters
    pPars->fTruth      =  1;
    pPars->fUsePerm    =  1; //!fUseSops;
    pPars->nLatches    =  0;
    pPars->pLutLib     =  NULL; // Abc_FrameReadLibLut();
    pPars->pTimesArr   =  NULL; 
    pPars->pTimesArr   =  NULL;   
    pPars->fUseBdds    =  fUseBdds;
    pPars->fUseSops    =  fUseSops;
    if ( fUseBdds )
        pPars->pFuncCost = Abc_NtkRenodeEvalBdd;
    else if ( fUseSops )
        pPars->pFuncCost = Abc_NtkRenodeEvalSop;
    else
        pPars->pFuncCost = Abc_NtkRenodeEvalAig;

    // start the manager
    if ( fUseBdds )
    {
        assert( s_pReo == NULL );
        s_pDd  = Cudd_Init( nFaninMax, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
        s_pReo = Extra_ReorderInit( nFaninMax, 100 );
        pPars->pReoMan  = s_pReo;
    }
    else
    {
        assert( s_vMemory == NULL );
        s_vMemory = Vec_IntAlloc( 1 << 16 );
    }

    // perform mapping/renoding
    pNtkNew = Abc_NtkIf( pNtk, pPars );

    // start the manager
    if ( fUseBdds )
    {
        Extra_StopManager( s_pDd );
        Extra_ReorderQuit( s_pReo );
        s_pReo = NULL;
        s_pDd  = NULL;
    }
    else
    {
        Vec_IntFree( s_vMemory );
        s_vMemory = NULL;
    }

    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Computes the cost based on the BDD size after reordering.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRenodeEvalBdd( If_Cut_t * pCut )
{
    int pOrder[IF_MAX_LUTSIZE];
    DdNode * bFunc, * bFuncNew;
    int i, k, nNodes;
    for ( i = 0; i < If_CutLeaveNum(pCut); i++ )
        pCut->pPerm[i] = pOrder[i] = -100;
    bFunc = Kit_TruthToBdd( s_pDd, If_CutTruth(pCut), If_CutLeaveNum(pCut), 0 );  Cudd_Ref( bFunc );
    bFuncNew = Extra_Reorder( s_pReo, s_pDd, bFunc, pOrder );                     Cudd_Ref( bFuncNew );
    for ( i = k = 0; i < If_CutLeaveNum(pCut); i++ )
        if ( pOrder[i] >= 0 )
            pCut->pPerm[pOrder[i]] = ++k; // double-check this!
    nNodes = -1 + Cudd_DagSize( bFuncNew );
    Cudd_RecursiveDeref( s_pDd, bFuncNew );
    Cudd_RecursiveDeref( s_pDd, bFunc );
    return nNodes; 
}

/**Function*************************************************************

  Synopsis    [Computes the cost based on ISOP.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRenodeEvalSop( If_Cut_t * pCut )
{
    int i, RetValue;
    for ( i = 0; i < If_CutLeaveNum(pCut); i++ )
        pCut->pPerm[i] = 1;
    RetValue = Kit_TruthIsop( If_CutTruth(pCut), If_CutLeaveNum(pCut), s_vMemory, 1 );
    if ( RetValue == -1 )
        return ABC_INFINITY;
    assert( RetValue == 0 || RetValue == 1 );
    return Vec_IntSize( s_vMemory );
}

/**Function*************************************************************

  Synopsis    [Computes the cost based on the factored form.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRenodeEvalAig( If_Cut_t * pCut )
{
    Kit_Graph_t * pGraph;
    int i, nNodes;
    pGraph = Kit_TruthToGraph( If_CutTruth(pCut), If_CutLeaveNum(pCut), s_vMemory );
    if ( pGraph == NULL )
    {
        for ( i = 0; i < If_CutLeaveNum(pCut); i++ )
            pCut->pPerm[i] = 100;
        return ABC_INFINITY;
    }
    nNodes = Kit_GraphNodeNum( pGraph );
    for ( i = 0; i < If_CutLeaveNum(pCut); i++ )
        pCut->pPerm[i] = Kit_GraphLeafDepth_rec( pGraph, Kit_GraphNodeLast(pGraph), Kit_GraphNode(pGraph, i) );
    Kit_GraphFree( pGraph );
    return nNodes;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


