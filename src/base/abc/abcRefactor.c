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
    int              nNodeSizeMax;  // the limit on the size of the supernode
    int              nConeSizeMax;  // the limit on the size of the containing cone
    int              fVerbose;      // the verbosity flag
    // internal parameters
    DdManager *      dd;            // the BDD manager
    Vec_Int_t *      vReqTimes;     // required times for each node
    Vec_Str_t *      vCube;         // temporary
    Vec_Int_t *      vForm;         // temporary
    Vec_Int_t *      vLevNums;      // temporary
    Vec_Ptr_t *      vVisited;      // temporary
    // runtime statistics
    int              time1;
    int              time2;
    int              time3;
};

static Abc_ManRef_t * Abc_NtkManRefStart( int nNodeSizeMax, int nConeSizeMax, int fVerbose );
static void           Abc_NtkManRefStop( Abc_ManRef_t * p );
static Vec_Int_t *    Abc_NodeRefactor( Abc_ManRef_t * p, Abc_Obj_t * pNode, Vec_Ptr_t * vFanins );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs incremental resynthesis of the AIG.]

  Description [Starting from each node, computes a reconvergence-driven cut, 
  derives BDD of the cut function, constructs ISOP, factors the cover, 
  and replaces the current implementation of the MFFC of the cut by the 
  new factored form if the number of AIG nodes is reduced. Returns the
  number of AIG nodes saved.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkRefactor( Abc_Ntk_t * pNtk, int nNodeSizeMax, int nConeSizeMax, bool fUseDcs, bool fVerbose )
{
    int fCheck = 1;
    ProgressBar * pProgress;
    Abc_ManRef_t * pManRef;
    Abc_ManCut_t * pManCut;
    Vec_Ptr_t * vFanins;
    Vec_Int_t * vForm;
    Abc_Obj_t * pNode;
    int i, nNodes;

    assert( Abc_NtkIsAig(pNtk) );
    // start the managers
    pManCut = Abc_NtkManCutStart( nNodeSizeMax, nConeSizeMax );
    pManRef = Abc_NtkManRefStart( nNodeSizeMax, nConeSizeMax, fVerbose );
    pManRef->vReqTimes = Abc_NtkGetRequiredLevels( pNtk );

    // resynthesize each node once
    nNodes = Abc_NtkObjNumMax(pNtk);
    pProgress = Extra_ProgressBarStart( stdout, nNodes );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        Extra_ProgressBarUpdate( pProgress, nNodes, NULL );
        // compute a reconvergence-driven cut
        vFanins = Abc_NodeFindCut( pManCut, pNode );
        // evaluate this cut
        vForm = Abc_NodeRefactor( pManRef, pNode, vFanins );
        // if acceptable replacement found, update the graph
        if ( vForm )
            Abc_NodeUpdate( pNode, vFanins, vForm, 0 );
        // check the improvement
        if ( i == nNodes )
            break;
    }
    Extra_ProgressBarStop( pProgress );

    // delete the managers
    Abc_NtkManCutStop( pManCut );
    Abc_NtkManRefStop( pManRef );
    // check
    if ( fCheck && !Abc_NtkCheck( pNtk ) )
    {
        printf( "Abc_NtkRewrite: The network check has failed.\n" );
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
Vec_Int_t * Abc_NodeRefactor( Abc_ManRef_t * p, Abc_Obj_t * pNode, Vec_Ptr_t * vFanins )
{
    Vec_Int_t * vForm;
    DdNode * bFuncNode;
    int nNodesSaved, RetValue;
    char * pSop;

    // get the cover
    bFuncNode = Abc_NodeConeBdd( p->dd, p->dd->vars, pNode, vFanins, p->vVisited );  Cudd_Ref( bFuncNode );
    pSop = Abc_ConvertBddToSop( NULL, p->dd, bFuncNode, bFuncNode, vFanins->nSize, p->vCube, -1 );
    Cudd_RecursiveDeref( p->dd, bFuncNode );
    // derive the factored form
    vForm = Ft_Factor( pSop );
    free( pSop );

    // label MFFC with current ID
    nNodesSaved = Abc_NodeMffcLabel( pNode );
    // detect how many unlabeled nodes will be reused
    RetValue = Abc_NodeStrashDecCount( pNode->pNtk->pManFunc, vFanins, vForm, 
        p->vLevNums, nNodesSaved, Vec_IntEntry( p->vReqTimes, pNode->Id ) );
    if ( RetValue >= 0 )
        return vForm;
    Vec_IntFree( vForm );
    return vForm;
}

/**Function*************************************************************

  Synopsis    [Starts the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_ManRef_t * Abc_NtkManRefStart( int nNodeSizeMax, int nConeSizeMax, int fVerbose )
{
    Abc_ManRef_t * p;
    p = ALLOC( Abc_ManRef_t, 1 );
    memset( p, 0, sizeof(Abc_ManRef_t) );
    p->vCube       = Vec_StrAlloc( 100 );
    p->vLevNums    = Vec_IntAlloc( 100 );
    p->vVisited    = Vec_PtrAlloc( 100 );
    p->nNodeSizeMax = nNodeSizeMax;
    p->nConeSizeMax = nConeSizeMax;
    p->fVerbose     = fVerbose;
    // start the BDD manager
    p->dd = Cudd_Init( p->nNodeSizeMax + p->nConeSizeMax, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
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
    Vec_IntFree( p->vReqTimes );
    Vec_PtrFree( p->vVisited );
    Vec_IntFree( p->vLevNums );
    Vec_StrFree( p->vCube    );
    free( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


