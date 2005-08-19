/**CFile****************************************************************

  FileName    [rwrMan.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [DAG-aware AIG rewriting package.]

  Synopsis    [Rewriting manager.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: rwrMan.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "rwr.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts rewriting manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Rwr_Man_t * Rwr_ManStart( bool fPrecompute )
{
    Rwr_Man_t * p;
    int clk = clock();
    p = ALLOC( Rwr_Man_t, 1 );
    memset( p, 0, sizeof(Rwr_Man_t) );
    p->nFuncs = (1<<16);
    // canonical forms, phases, perms
clk = clock();
    Extra_Truth4VarNPN( &p->puCanons, &p->pPhases, &p->pPerms, &p->pMap );
PRT( "NPN classes precomputation time", clock() - clk ); 
    // initialize practical NPN classes
    p->pPractical  = Rwr_ManGetPractical( p );
    // create the table
    p->pTable = ALLOC( Rwr_Node_t *, p->nFuncs );
    memset( p->pTable, 0, sizeof(Rwr_Node_t *) * p->nFuncs );
    // create the elementary nodes
    assert( sizeof(Rwr_Node_t) == sizeof(Rwr_Cut_t) );
    p->pMmNode  = Extra_MmFixedStart( sizeof(Rwr_Node_t) );
    p->vForest  = Vec_PtrAlloc( 100 );
    Rwr_ManAddVar( p, 0x0000, fPrecompute ); // constant 0
    Rwr_ManAddVar( p, 0xAAAA, fPrecompute ); // var A
    Rwr_ManAddVar( p, 0xCCCC, fPrecompute ); // var B
    Rwr_ManAddVar( p, 0xF0F0, fPrecompute ); // var C
    Rwr_ManAddVar( p, 0xFF00, fPrecompute ); // var D
    p->nClasses = 5;
    // other stuff
    p->nTravIds = 1;
    p->puPerms43 = Extra_TruthPerm43();
    p->vLevNums  = Vec_IntAlloc( 50 );
    p->vFanins   = Vec_PtrAlloc( 50 );
    if ( fPrecompute )
    {   // precompute subgraphs
        Rwr_ManPrecompute( p );
        Rwr_ManWriteToArray( p );
        Rwr_ManPrint( p );
    }
    else
    {   // load saved subgraphs
        Rwr_ManLoadFromArray( p );
//        Rwr_ManPrint( p );
        Rwr_ManPreprocess( p );
        return NULL;
    }
    return p;
}

/**Function*************************************************************

  Synopsis    [Stops rewriting manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_ManStop( Rwr_Man_t * p )
{
    if ( p->vClasses )
    {
        Rwr_Node_t * pNode;
        int i, k;
        Vec_VecForEachEntry( p->vClasses, pNode, i, k )
            Vec_IntFree( (Vec_Int_t *)pNode->pNext );
    }
    if ( p->vFanNums )  Vec_IntFree( p->vFanNums );
    if ( p->vReqTimes ) Vec_IntFree( p->vReqTimes );
    if ( p->vClasses )  Vec_VecFree( p->vClasses );
    Vec_PtrFree( p->vForest );
    Vec_IntFree( p->vLevNums );
    Vec_PtrFree( p->vFanins );
    Extra_MmFixedStop( p->pMmNode, 0 );
    free( p->pTable );
    free( p->pPractical );
    free( p->puPerms43 );
    free( p->puCanons );
    free( p->pPhases );
    free( p->pPerms );
    free( p->pMap );
    free( p );
}

/**Function*************************************************************

  Synopsis    [Assigns elementary cuts to the PIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_ManPrepareNetwork( Rwr_Man_t * p, Abc_Ntk_t * pNtk )
{
    // save the fanout counters for all internal nodes
    p->vFanNums = Rwt_NtkFanoutCounters( pNtk );
    // precompute the required times for all internal nodes
    p->vReqTimes = Abc_NtkGetRequiredLevels( pNtk );
    // start the cut computation
    Rwr_NtkStartCuts( p, pNtk );
}

/**Function*************************************************************

  Synopsis    [Stops the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Rwr_ManReadFanins( Rwr_Man_t * p )
{
    return p->vFanins;
}

/**Function*************************************************************

  Synopsis    [Stops the resynthesis manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Rwr_ManReadDecs( Rwr_Man_t * p )
{
    return p->vForm;
}


/**Function*************************************************************

  Synopsis    [Precomputes AIG subgraphs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Rwr_Precompute()
{
    Rwr_Man_t * p;
    p = Rwr_ManStart( 1 );
    Rwr_ManStop( p );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


