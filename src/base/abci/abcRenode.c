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

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static int Abc_NtkRenodeEvalBdd( unsigned * pTruth, int nVars );
static int Abc_NtkRenodeEvalSop( unsigned * pTruth, int nVars );

static reo_man * s_pReo = NULL;
static DdManager * s_pDd  = NULL;

typedef int Kit_Graph_t;
extern DdNode * Kit_TruthToBdd( DdManager * dd, unsigned * pTruth, int nVars );
extern Kit_Graph_t * Kit_TruthToGraph( unsigned * pTruth, int nVars );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs renoding as technology mapping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkRenode( Abc_Ntk_t * pNtk, int nFaninMax, int fUseBdds, int fVerbose )
{
    extern Abc_Ntk_t * Abc_NtkIf( Abc_Ntk_t * pNtk, If_Par_t * pPars );
    If_Par_t Pars, * pPars = &Pars;
    Abc_Ntk_t * pNtkNew;

    // set defaults
    memset( pPars, 0, sizeof(If_Par_t) );
    // user-controlable paramters
    pPars->Mode        =  0;
    pPars->nLutSize    =  nFaninMax;
    pPars->nCutsMax    = 10;
    pPars->DelayTarget = -1;
    pPars->fPreprocess =  1;
    pPars->fArea       =  0;
    pPars->fFancy      =  0;
    pPars->fExpRed     =  0; //
    pPars->fLatchPaths =  0;
    pPars->fSeq        =  0;
    pPars->fVerbose    =  0;
    // internal parameters
    pPars->fTruth      =  1;
    pPars->nLatches    =  0;
    pPars->pLutLib     =  NULL; // Abc_FrameReadLibLut();
    pPars->pTimesArr   =  NULL; 
    pPars->pTimesArr   =  NULL;   
    pPars->pFuncCost   =  fUseBdds? Abc_NtkRenodeEvalBdd : Abc_NtkRenodeEvalSop;   

    // start the manager
    if ( fUseBdds )
    {
        assert( s_pReo == NULL );
        s_pDd  = Cudd_Init( nFaninMax, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
        s_pReo = Extra_ReorderInit( nFaninMax, 100 );
        pPars->fUseBdds = 1;
        pPars->pReoMan  = s_pReo;
    }

    // perform mapping/renoding
    pNtkNew = Abc_NtkIf( pNtk, pPars );

    // start the manager
    if ( fUseBdds )
    {
        Extra_StopManager( s_pDd );
        Extra_ReorderQuit( s_pReo );
        s_pReo = NULL;
        s_pDd = NULL;
    }
    return pNtkNew;
}

/**Function*************************************************************

  Synopsis    [Derives the BDD after reordering.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRenodeEvalBdd( unsigned * pTruth, int nVars )
{
    DdNode * bFunc, * bFuncNew;
    int nNodes, nSupport;
    bFunc = Kit_TruthToBdd( s_pDd, pTruth, nVars );           Cudd_Ref( bFunc );
    bFuncNew = Extra_Reorder( s_pReo, s_pDd, bFunc, NULL );   Cudd_Ref( bFuncNew );
    nSupport = Cudd_SupportSize( s_pDd, bFuncNew );
    nNodes = Cudd_DagSize( bFuncNew );
    Cudd_RecursiveDeref( s_pDd, bFuncNew );
    Cudd_RecursiveDeref( s_pDd, bFunc );
    return (nSupport << 16) | nNodes;
}

/**Function*************************************************************

  Synopsis    [Derives the BDD after reordering.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRenodeEvalSop( unsigned * pTruth, int nVars )
{
    Kit_Graph_t * pGraph;
    int nNodes, nDepth;
    pGraph = Kit_TruthToGraph( pTruth, nVars );
    nNodes = Kit_GraphNodeNum( pGraph );
    nDepth = Kit_GraphLevelNum( pGraph );
    Kit_GraphFree( pGraph );
    return (nDepth << 16) | nNodes;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


