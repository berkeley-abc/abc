/**CFile****************************************************************

  FileName    [sswSweep.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Inductive prover with constraints.]

  Synopsis    [One round of SAT sweeping.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 1, 2008.]

  Revision    [$Id: sswSweep.c,v 1.00 2008/09/01 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sswInt.h"
#include "bar.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Performs fraiging for one node.]

  Description [Returns the fraiged node.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ManSweepNode( Ssw_Man_t * p, Aig_Obj_t * pObj, int f )
{ 
    Aig_Obj_t * pObjRepr, * pObjFraig, * pObjFraig2, * pObjReprFraig;
    int RetValue;
    // get representative of this class
    pObjRepr = Aig_ObjRepr( p->pAig, pObj );
    if ( pObjRepr == NULL )
        return;
    // get the fraiged node
    pObjFraig = Ssw_ObjFraig( p, pObj, f );
    if ( pObjFraig == NULL )
        return;
    // get the fraiged representative
    pObjReprFraig = Ssw_ObjFraig( p, pObjRepr, f );
    if ( pObjReprFraig == NULL )
        return;
    // if the fraiged nodes are the same, return
    if ( Aig_Regular(pObjFraig) == Aig_Regular(pObjReprFraig) )
    {
        // remember the proved equivalence
//        p->pReprsProved[ pObj->Id ] = pObjRepr;
        return;
    }
    assert( Aig_Regular(pObjFraig) != Aig_ManConst1(p->pFrames) );
    RetValue = Ssw_NodesAreEquiv( p, Aig_Regular(pObjReprFraig), Aig_Regular(pObjFraig) );
    if ( RetValue == -1 ) // timed out
    {
        Ssw_ClassesRemoveNode( p->ppClasses, pObj );
        p->fRefined = 1;
        return;
    }
    if ( RetValue == 1 )  // proved equivalent
    {
        pObjFraig2 = Aig_NotCond( pObjReprFraig, pObj->fPhase ^ pObjRepr->fPhase );
        Ssw_ObjSetFraig( p, pObj, f, pObjFraig2 );
        // remember the proved equivalence
//        p->pReprsProved[ pObj->Id ] = pObjRepr;
        return;
    }
    // disproved the equivalence
    Ssw_ManResimulateCex( p, pObj, pObjRepr, f );
    assert( Aig_ObjRepr( p->pAig, pObj ) != pObjRepr );
    p->fRefined = 1;
}

/**Function*************************************************************

  Synopsis    [Performs fraiging for the internal nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ssw_ManSweepBmc( Ssw_Man_t * p )
{
    Bar_Progress_t * pProgress = NULL;
    Aig_Obj_t * pObj, * pObjNew;
    int i, f, clk;
clk = clock();

    // start initialized timeframes
    p->pFrames = Aig_ManStart( Aig_ManObjNumMax(p->pAig) * p->pPars->nFramesK );
    Saig_ManForEachLo( p->pAig, pObj, i )
        Ssw_ObjSetFraig( p, pObj, 0, Aig_ManConst0(p->pFrames) );

    // sweep internal nodes
    p->fRefined = 0;
    pProgress = Bar_ProgressStart( stdout, Aig_ManObjNumMax(p->pAig) * p->pPars->nFramesK );
    for ( f = 0; f < p->pPars->nFramesK; f++ )
    {
        // map constants and PIs
        Ssw_ObjSetFraig( p, Aig_ManConst1(p->pAig), f, Aig_ManConst1(p->pFrames) );
        Saig_ManForEachPi( p->pAig, pObj, i )
            Ssw_ObjSetFraig( p, pObj, f, Aig_ObjCreatePi(p->pFrames) );
        // sweep internal nodes
        Aig_ManForEachNode( p->pAig, pObj, i )
        {
            Bar_ProgressUpdate( pProgress, Aig_ManObjNumMax(p->pAig) * f + i, NULL );
            pObjNew = Aig_And( p->pFrames, Ssw_ObjChild0Fra(p, pObj, f), Ssw_ObjChild1Fra(p, pObj, f) );
            Ssw_ObjSetFraig( p, pObj, f, pObjNew );
            Ssw_ManSweepNode( p, pObj, f );
        }
    }
    Bar_ProgressStop( pProgress );

    // cleanup
    Ssw_ClassesCheck( p->ppClasses );
    Ssw_ManCleanup( p );
p->timeBmc += clock() - clk;
    return p->fRefined;
}

/**Function*************************************************************

  Synopsis    [Performs fraiging for the internal nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ssw_ManSweep( Ssw_Man_t * p )
{
    Bar_Progress_t * pProgress = NULL;
    Aig_Obj_t * pObj, * pObj2, * pObjNew;
    int nConstrPairs, clk, i, f = p->pPars->nFramesK;

    // perform speculative reduction
clk = clock();
    // create timeframes
    p->pFrames = Ssw_FramesWithClasses( p );
    p->nFrameNodes = Aig_ManNodeNum( p->pFrames );
    // add constraints
    nConstrPairs = Aig_ManPoNum(p->pFrames)-Aig_ManRegNum(p->pAig);
    assert( (nConstrPairs & 1) == 0 );
    for ( i = 0; i < nConstrPairs; i += 2 )
    {
        pObj  = Aig_ManPo( p->pFrames, i   );
        pObj2 = Aig_ManPo( p->pFrames, i+1 );
        Ssw_NodesAreConstrained( p, Aig_ObjFanin0(pObj), Aig_ObjFanin0(pObj2) );
    }
    // build logic cones for register inputs
    for ( i = 0; i < Aig_ManRegNum(p->pAig); i++ )
    {
        pObj  = Aig_ManPo( p->pFrames, nConstrPairs + i );
        Ssw_CnfNodeAddToSolver( p, Aig_ObjFanin0(pObj) );
    }
    sat_solver_simplify( p->pSat );
p->timeReduce += clock() - clk;

    // map constants and PIs
    Ssw_ObjSetFraig( p, Aig_ManConst1(p->pAig), f, Aig_ManConst1(p->pFrames) );
    Saig_ManForEachPi( p->pAig, pObj, i )
        Ssw_ObjSetFraig( p, pObj, f, Aig_ObjCreatePi(p->pFrames) );
    // sweep internal nodes
    p->fRefined = 0;
    pProgress = Bar_ProgressStart( stdout, Aig_ManObjNumMax(p->pAig) );
    Aig_ManForEachNode( p->pAig, pObj, i )
    {
        Bar_ProgressUpdate( pProgress, i, NULL );
        pObjNew = Aig_And( p->pFrames, Ssw_ObjChild0Fra(p, pObj, f), Ssw_ObjChild1Fra(p, pObj, f) );
        Ssw_ObjSetFraig( p, pObj, f, pObjNew );
        Ssw_ManSweepNode( p, pObj, f );
    }
    Bar_ProgressStop( pProgress );

    // cleanup
    Ssw_ClassesCheck( p->ppClasses );
    Ssw_ManCleanup( p );
    return p->fRefined;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


