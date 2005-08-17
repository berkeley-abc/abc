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

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
 
struct Abc_ManRef_t_
{
    // user specified parameters
    int              nNodeSizeMax;  // the limit on the size of the supernode
    int              nConeSizeMax;  // the limit on the size of the containing cone
    int              fVerbose;      // the verbosity flag
    // the node currently processed
    Abc_Obj_t *      pNode;         // the node currently considered
    // internal parameters
    DdManager *      dd;            // the BDD manager
    DdNode *         bCubeX;        // the cube of PI variables
    Vec_Str_t *      vCube;         // temporary cube for generating covers
    Vec_Int_t *      vForm;         // the factored form (temporary)
    // runtime statistics
    int              time1;
    int              time2;
    int              time3;
    int              time4;
};

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Resynthesizes the node using refactoring.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
bool Abc_NodeRefactor( Abc_ManRef_t * p, Abc_Obj_t * pNode )
{
    return 0;
}

/**Function*************************************************************

  Synopsis    [Derives the factored form of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
/*
Vec_Int_t * Abc_NodeRefactor( Abc_ManRef_t * p )
{
    Vec_Int_t * vForm;
    DdManager * dd = p->dd;
    DdNode * bFuncNode, * bFuncCone, * bCare, * bFuncOn, * bFuncOnDc;
    char * pSop;
    int nFanins;

    assert( p->vFaninsNode->nSize < p->nNodeSizeMax );
    assert( p->vFaninsCone->nSize < p->nConeSizeMax );

    // get the function of the node
    bFuncNode = Abc_NodeConeBdd( dd, p->dd->vars, p->pNode, p->vFaninsNode, p->vVisited );  
    Cudd_Ref( bFuncNode );
    nFanins = p->vFaninsNode->nSize;
    if ( p->nConeSizeMax > p->nNodeSizeMax )
    {
        // get the function of the cone
        bFuncCone = Abc_NodeConeBdd( dd, p->dd->vars + p->nNodeSizeMax, p->pNode, p->vFaninsCone, p->vVisited );  
        Cudd_Ref( bFuncCone );
        // get the care set
        bCare = Cudd_bddXorExistAbstract( p->dd, Cudd_Not(bFuncNode), bFuncCone, p->bCubeX );   Cudd_Ref( bCare );
        Cudd_RecursiveDeref( dd, bFuncCone );
        // compute the on-set and off-set of the function of the node
        bFuncOn   = Cudd_bddAnd( dd, bFuncNode, bCare );                Cudd_Ref( bFuncOn );
        bFuncOnDc = Cudd_bddAnd( dd, Cudd_Not(bFuncNode), bCare );      Cudd_Ref( bFuncOnDc );
        bFuncOnDc = Cudd_Not( bFuncOnDc );
        Cudd_RecursiveDeref( dd, bCare );
        // get the cover
        pSop = Abc_ConvertBddToSop( NULL, dd, bFuncOn, bFuncOnDc, nFanins, p->vCube, -1 );
        Cudd_RecursiveDeref( dd, bFuncOn );
        Cudd_RecursiveDeref( dd, bFuncOnDc );
    }
    else
    {
        // get the cover
        pSop = Abc_ConvertBddToSop( NULL, dd, bFuncNode, bFuncNode, nFanins, p->vCube, -1 );
    }
    Cudd_RecursiveDeref( dd, bFuncNode );
    // derive the factored form
    vForm = Ft_Factor( pSop );
    free( pSop );
    return vForm;
}
*/


/**Function*************************************************************

  Synopsis    [Starts the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_ManRef_t * Abc_NtkManRefStart()
{
    Abc_ManRef_t * p;
    p = ALLOC( Abc_ManRef_t, 1 );
    memset( p, 0, sizeof(Abc_ManRef_t) );
    p->vCube       = Vec_StrAlloc( 100 );
    

    // start the BDD manager
    p->dd = Cudd_Init( p->nNodeSizeMax + p->nConeSizeMax, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
    Cudd_zddVarsFromBddVars( p->dd, 2 );
    p->bCubeX = Extra_bddComputeRangeCube( p->dd, p->nNodeSizeMax, p->dd->size );   Cudd_Ref( p->bCubeX );

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
    if ( p->bCubeX ) Cudd_RecursiveDeref( p->dd, p->bCubeX );
    if ( p->dd )     Extra_StopManager( p->dd );
    Vec_StrFree( p->vCube       );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Stops the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_NtkManRefResult( Abc_ManRef_t * p )
{
    return p->vForm;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


