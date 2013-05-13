/**CFile****************************************************************

  FileName    [sfmWin.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based optimization using internal don't-cares.]

  Synopsis    [Structural window computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: sfmWin.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sfmInt.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Working with traversal IDs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void  Sfm_NtkIncrementTravId( Sfm_Ntk_t * p )            { p->nTravIds++;                                           }       
static inline void  Sfm_ObjSetTravIdCurrent( Sfm_Ntk_t * p, int Id )   { Vec_IntWriteEntry( &p->vTravIds, Id, p->nTravIds );      }
static inline int   Sfm_ObjIsTravIdCurrent( Sfm_Ntk_t * p, int Id )    { return (Vec_IntEntry(&p->vTravIds, Id) == p->nTravIds);  }   

/**Function*************************************************************

  Synopsis    [Computes structural window.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_NtkCollectTfi_rec( Sfm_Ntk_t * p, int iNode )
{
    int i, iFanin;
    if ( Sfm_ObjIsTravIdCurrent( p, iNode ) )
        return;
    Sfm_ObjSetTravIdCurrent( p, iNode );
    if ( Sfm_ObjIsPi( p, iNode ) )
    {
        Vec_IntPush( p->vLeaves, iNode );
        return;
    }
    Sfm_NodeForEachFanin( p, iNode, iFanin, i )
        Sfm_NtkCollectTfi_rec( p, iFanin );
    Vec_IntPush( p->vNodes, iNode );
}
int Sfm_NtkWindow( Sfm_Ntk_t * p, int iNode )
{
//    int i, iRoot;
    assert( Sfm_ObjIsNode( p, iNode ) );
    Sfm_NtkIncrementTravId( p );
    Vec_IntClear( p->vLeaves ); // leaves 
    Vec_IntClear( p->vNodes );  // internal
    // collect transitive fanin
    Sfm_NtkCollectTfi_rec( p, iNode );
    // collect TFO
    Vec_IntClear( p->vRoots );  // roots
    Vec_IntClear( p->vTfo );    // roots
    Vec_IntPush( p->vRoots, iNode );
/*
    Vec_IntForEachEntry( p->vRoots, iRoot, i )
    {
        assert( Sfm_ObjIsNode(p, iRoot) );
        if ( Sfm_ObjIsTravIdCurrent(p, iRoot) )
            continue;
        if ( Sfm_ObjFanoutNum(p, iRoot) >= p->pPars->nFanoutMax )
            continue;
    }
*/
    return 1;
}

/**Function*************************************************************

  Synopsis    [Converts a window into a SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Sfm_NtkWin2Sat( Sfm_Ntk_t * p )
{
    Vec_Int_t * vClause;
    int RetValue, Lit, iNode, iFanin, i, k;
    sat_solver * pSat0 = sat_solver_new();
    sat_solver * pSat1 = sat_solver_new();
    sat_solver_setnvars( pSat0, 1 + Vec_IntSize(p->vLeaves) + Vec_IntSize(p->vNodes) + 2 * Vec_IntSize(p->vTfo) + Vec_IntSize(p->vRoots) );
    sat_solver_setnvars( pSat1, 1 + Vec_IntSize(p->vLeaves) + Vec_IntSize(p->vNodes) + 2 * Vec_IntSize(p->vTfo) + Vec_IntSize(p->vRoots) );
    // create SAT variables
    p->nSatVars = 1;
    Vec_IntForEachEntryReverse( p->vNodes, iNode, i )
        Sfm_ObjSetSatVar( p, iNode, p->nSatVars++ );
    Vec_IntForEachEntryReverse( p->vLeaves, iNode, i )
        Sfm_ObjSetSatVar( p, iNode, p->nSatVars++ );
    // add CNF clauses
    Vec_IntForEachEntryReverse( p->vNodes, iNode, i )
    {
        // collect fanin variables
        Vec_IntClear( p->vFaninMap );
        Sfm_NodeForEachFanin( p, iNode, iFanin, k )
            Vec_IntPush( p->vFaninMap, Sfm_ObjSatVar(p, iFanin) );
        Vec_IntPush( p->vFaninMap, Sfm_ObjSatVar(p, iNode) );
        // generate CNF 
        Sfm_TranslateCnf( p->vClauses, (Vec_Str_t *)Vec_WecEntry(p->vCnfs, iNode), p->vFaninMap );
        // add clauses
        Vec_WecForEachLevel( p->vClauses, vClause, k )
        {
            if ( Vec_IntSize(vClause) == 0 )
                break;
            RetValue = sat_solver_addclause( pSat0, Vec_IntArray(vClause), Vec_IntArray(vClause) + Vec_IntSize(vClause) );
            assert( RetValue );
            RetValue = sat_solver_addclause( pSat1, Vec_IntArray(vClause), Vec_IntArray(vClause) + Vec_IntSize(vClause) );
            assert( RetValue );
        }
    }
    // add unit clause
    Lit = Abc_Var2Lit( Sfm_ObjSatVar(p, iNode), 1 );
    RetValue = sat_solver_addclause( pSat0, &Lit, &Lit + 1 );
    assert( RetValue );
    // add unit clause
    Lit = Abc_Var2Lit( Sfm_ObjSatVar(p, iNode), 0 );
    RetValue = sat_solver_addclause( pSat1, &Lit, &Lit + 1 );
    assert( RetValue );
    // finalize
    sat_solver_compress( p->pSat0 );
    sat_solver_compress( p->pSat1 );
    // return the result
    assert( p->pSat0 == NULL );
    assert( p->pSat1 == NULL );
    p->pSat0 = pSat0;
    p->pSat1 = pSat1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

