/**CFile****************************************************************

  FileName    [abcResRef.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Resynthesis based on refactoring.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcResRef.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "ft.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
 
typedef struct Abc_ManRef_t_   Abc_ManRef_t;
struct Abc_ManRef_t_
{
    // user specified parameters
    int              nNodeSizeMax;      // the limit on the size of the supernode
    int              nConeSizeMax;      // the limit on the size of the containing cone
    int              fVerbose;          // the verbosity flag
    // internal data structures
    DdManager *      dd;                // the BDD manager
//    Vec_Int_t *      vReqTimes;         // required times for each node
    Vec_Str_t *      vCube;             // temporary
    Vec_Int_t *      vForm;             // temporary
    Vec_Int_t *      vLevNums;          // temporary
    Vec_Ptr_t *      vVisited;          // temporary
    Vec_Ptr_t *      vLeaves;           // temporary
    // node statistics
    int              nLastGain;
    int              nNodesConsidered;
    int              nNodesRefactored;
    int              nNodesGained;
    // runtime statistics
    int              timeCut;
    int              timeBdd;
    int              timeDcs;
    int              timeSop;
    int              timeFact;
    int              timeEval;
    int              timeRes;
    int              timeNtk;
    int              timeTotal;
};
 
static void           Abc_NtkManRefPrintStats( Abc_ManRef_t * p );
static Abc_ManRef_t * Abc_NtkManRefStart( int nNodeSizeMax, int nConeSizeMax, bool fUseDcs, bool fVerbose );
static void           Abc_NtkManRefStop( Abc_ManRef_t * p );
static Vec_Int_t *    Abc_NodeRefactor( Abc_ManRef_t * p, Abc_Obj_t * pNode, Vec_Ptr_t * vFanins, bool fUseZeros, bool fUseDcs, bool fVerbose );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs incremental resynthesis of the AIG.]

  Description [Starting from each node, computes a reconvergence-driven cut, 
  derives BDD of the cut function, constructs ISOP, factors the ISOP, 
  and replaces the current implementation of the MFFC of the node by the 
  new factored form, if the number of AIG nodes is reduced and the total
  number of levels of the AIG network is not increated. Returns the
  number of AIG nodes saved.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRefactor( Abc_Ntk_t * pNtk, int nNodeSizeMax, int nConeSizeMax, bool fUseZeros, bool fUseDcs, bool fVerbose )
{
    int fCheck = 1;
    ProgressBar * pProgress;
    Abc_ManRef_t * pManRef;
    Abc_ManCut_t * pManCut;
    Vec_Ptr_t * vFanins;
    Vec_Int_t * vForm;
    Abc_Obj_t * pNode;
    int i, nNodes;
    int clk, clkStart = clock();

    assert( Abc_NtkIsStrash(pNtk) );
    // start the managers
    pManCut = Abc_NtkManCutStart( nNodeSizeMax, nConeSizeMax );
    pManRef = Abc_NtkManRefStart( nNodeSizeMax, nConeSizeMax, fUseDcs, fVerbose );
    pManRef->vLeaves   = Abc_NtkManCutReadLeaves( pManCut );
    Abc_NtkStartReverseLevels( pNtk );

    // resynthesize each node once
    nNodes = Abc_NtkObjNumMax(pNtk);
    pProgress = Extra_ProgressBarStart( stdout, nNodes );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        // stop if all nodes have been tried once
        if ( i >= nNodes )
            break;
        // skip the constant node
        if ( Abc_NodeIsConst(pNode) )
            continue;
        // compute a reconvergence-driven cut
clk = clock();
        vFanins = Abc_NodeFindCut( pManCut, pNode, fUseDcs );
pManRef->timeCut += clock() - clk;
        // evaluate this cut
clk = clock();
        vForm = Abc_NodeRefactor( pManRef, pNode, vFanins, fUseZeros, fUseDcs, fVerbose );
pManRef->timeRes += clock() - clk;
        if ( vForm == NULL )
            continue;
        // acceptable replacement found, update the graph
clk = clock();
        Abc_NodeUpdate( pNode, vFanins, vForm, pManRef->nLastGain );
pManRef->timeNtk += clock() - clk;
        Vec_IntFree( vForm );
    }
    Extra_ProgressBarStop( pProgress );
pManRef->timeTotal = clock() - clkStart;

    // print statistics of the manager
    if ( fVerbose )
        Abc_NtkManRefPrintStats( pManRef );
    // delete the managers
    Abc_NtkManCutStop( pManCut );
    Abc_NtkManRefStop( pManRef );
    Abc_NtkStopReverseLevels( pNtk );
    // check
    if ( fCheck && !Abc_NtkCheck( pNtk ) )
    {
        printf( "Abc_NtkRefactor: The network check has failed.\n" );
        return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Resynthesizes the node using refactoring.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_NodeRefactor( Abc_ManRef_t * p, Abc_Obj_t * pNode, Vec_Ptr_t * vFanins, bool fUseZeros, bool fUseDcs, bool fVerbose )
{
    int fVeryVerbose = 0;
    Abc_Obj_t * pFanin;
    Vec_Int_t * vForm;
    DdNode * bNodeFunc, * bNodeDc, * bNodeOn, * bNodeOnDc;
    char * pSop;
    int nBddNodes, nFtNodes, nNodesSaved, nNodesAdded;
    int i, Required, clk;

    p->nNodesConsidered++;

    // get the required level of this node
    Required = Abc_NodeReadRequiredLevel( pNode );

    // get the function of the cut
clk = clock();
    bNodeFunc = Abc_NodeConeBdd( p->dd, p->dd->vars, pNode, vFanins, p->vVisited );  Cudd_Ref( bNodeFunc );
p->timeBdd += clock() - clk;
    nBddNodes = Cudd_DagSize(bNodeFunc);

    // if don't-care are used, transform the function into ISOP
    if ( fUseDcs )
    {
        int nMints, nMintsDc;

clk = clock();
        // get the don't-cares
        bNodeDc = Abc_NodeConeDcs( p->dd, p->dd->vars + vFanins->nSize, p->dd->vars, p->vLeaves, vFanins, p->vVisited ); Cudd_Ref( bNodeDc );

        nMints = (1 << vFanins->nSize);
        nMintsDc = (int)Cudd_CountMinterm( p->dd, bNodeDc, vFanins->nSize );
//        printf( "Percentage of minterms = %5.2f.\n", 100.0 * nMintsDc / nMints );

        // get the ISF
        bNodeOn   = Cudd_bddAnd( p->dd, bNodeFunc, Cudd_Not(bNodeDc) );   Cudd_Ref( bNodeOn );
        bNodeOnDc = Cudd_bddOr ( p->dd, bNodeFunc, bNodeDc );             Cudd_Ref( bNodeOnDc );
        Cudd_RecursiveDeref( p->dd, bNodeFunc );
        Cudd_RecursiveDeref( p->dd, bNodeDc );
        // get the ISOP
        bNodeFunc = Cudd_bddIsop( p->dd, bNodeOn, bNodeOnDc );            Cudd_Ref( bNodeFunc );
        Cudd_RecursiveDeref( p->dd, bNodeOn );
        Cudd_RecursiveDeref( p->dd, bNodeOnDc );
p->timeDcs += clock() - clk;
    }

//Extra_bddPrint( p->dd, bNodeFunc ); printf( "\n" );
    // always accept the case of constant node
    if ( Cudd_IsConstant(bNodeFunc) )
    {
        p->nLastGain = Abc_NodeMffcSize( pNode );
        p->nNodesGained += p->nLastGain;
        p->nNodesRefactored++;
        // get the constant node
//        pFanin = Abc_ObjNotCond( Abc_AigConst1(pNode->pNtk->pManFunc), Cudd_IsComplement(bNodeFunc) );
//        Abc_AigReplace( pNode->pNtk->pManFunc, pNode, pFanin );
//        Cudd_RecursiveDeref( p->dd, bNodeFunc );
//printf( "Gain = %d.\n", p->nLastGain );
        Cudd_RecursiveDeref( p->dd, bNodeFunc );
        return Ft_FactorConst( !Cudd_IsComplement(bNodeFunc) );
    }

    // get the SOP of the cut
clk = clock();
    pSop = Abc_ConvertBddToSop( NULL, p->dd, bNodeFunc, bNodeFunc, vFanins->nSize, p->vCube, -1 );
p->timeSop += clock() - clk;
    Cudd_RecursiveDeref( p->dd, bNodeFunc );

    // get the factored form
clk = clock();
    vForm = Ft_Factor( pSop );
p->timeFact += clock() - clk;
    nFtNodes = Ft_FactorGetNumNodes( vForm );
    free( pSop );
//Ft_FactorPrint( stdout, vForm, NULL, NULL );

    // mark the fanin boundary 
    // (can mark only essential fanins, belonging to bNodeFunc!!!)
    Vec_PtrForEachEntry( vFanins, pFanin, i )
        pFanin->vFanouts.nSize++;

    // label MFFC with current traversal ID
    Abc_NtkIncrementTravId( pNode->pNtk );
    nNodesSaved = Abc_NodeMffcLabel( pNode );

    // unmark the fanin boundary
    Vec_PtrForEachEntry( vFanins, pFanin, i )
        pFanin->vFanouts.nSize--;

    // detect how many new nodes will be added (while taking into account reused nodes)
clk = clock();
    nNodesAdded = Abc_NodeStrashDecCount( pNode->pNtk->pManFunc, pNode, vFanins, vForm, 
        p->vLevNums, nNodesSaved, Required );
p->timeEval += clock() - clk;
    // quit if there is no improvement
    if ( nNodesAdded == -1 || nNodesAdded == nNodesSaved && !fUseZeros )
    {
        Vec_IntFree( vForm );
        return NULL;
    }

    // compute the total gain in the number of nodes
    p->nLastGain = nNodesSaved - nNodesAdded;
    p->nNodesGained += p->nLastGain;
    p->nNodesRefactored++;

    // report the progress
    if ( fVeryVerbose )
    {
        printf( "Node %6s : ",  Abc_ObjName(pNode) );
        printf( "Cone = %2d. ", vFanins->nSize );
        printf( "BDD = %2d. ",  nBddNodes );
        printf( "FF = %2d. ",   nFtNodes );
        printf( "MFFC = %2d. ", nNodesSaved );
        printf( "Add = %2d. ",  nNodesAdded );
        printf( "GAIN = %2d. ", p->nLastGain );
        printf( "\n" );
    }
    return vForm;
}


/**Function*************************************************************

  Synopsis    [Starts the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_ManRef_t * Abc_NtkManRefStart( int nNodeSizeMax, int nConeSizeMax, bool fUseDcs, bool fVerbose )
{
    Abc_ManRef_t * p;
    p = ALLOC( Abc_ManRef_t, 1 );
    memset( p, 0, sizeof(Abc_ManRef_t) );
    p->vCube        = Vec_StrAlloc( 100 );
    p->vLevNums     = Vec_IntAlloc( 100 );
    p->vVisited     = Vec_PtrAlloc( 100 );
    p->nNodeSizeMax = nNodeSizeMax;
    p->nConeSizeMax = nConeSizeMax;
    p->fVerbose     = fVerbose;
    // start the BDD manager
    if ( fUseDcs )
        p->dd = Cudd_Init( p->nNodeSizeMax + p->nConeSizeMax, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
    else
        p->dd = Cudd_Init( p->nNodeSizeMax, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
    Cudd_zddVarsFromBddVars( p->dd, 2 );
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkManRefStop( Abc_ManRef_t * p )
{
    Extra_StopManager( p->dd );
//    Vec_IntFree( p->vReqTimes );
    Vec_PtrFree( p->vVisited );
    Vec_IntFree( p->vLevNums );
    Vec_StrFree( p->vCube    );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Stops the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkManRefPrintStats( Abc_ManRef_t * p )
{
    printf( "Refactoring statistics:\n" );
    printf( "Nodes considered  = %8d.\n", p->nNodesConsidered );
    printf( "Nodes refactored  = %8d.\n", p->nNodesRefactored );
    printf( "Calculated gain   = %8d.\n", p->nNodesGained     );
    PRT( "Cuts       ", p->timeCut );
    PRT( "Resynthesis", p->timeRes );
    PRT( "    BDD    ", p->timeBdd );
    PRT( "    DCs    ", p->timeDcs );
    PRT( "    SOP    ", p->timeSop );
    PRT( "    FF     ", p->timeFact );
    PRT( "    Eval   ", p->timeEval );
    PRT( "AIG update ", p->timeNtk );
    PRT( "TOTAL      ", p->timeTotal );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


