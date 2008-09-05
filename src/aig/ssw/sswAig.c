/**CFile****************************************************************

  FileName    [sswAig.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Inductive prover with constraints.]

  Synopsis    [AIG manipulation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 1, 2008.]

  Revision    [$Id: sswAig.c,v 1.00 2008/09/01 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sswInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////


/**Function*************************************************************

  Synopsis    [Performs speculative reduction for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Ssw_FramesConstrainNode( Ssw_Man_t * p, Aig_Man_t * pFrames, Aig_Man_t * pAig, Aig_Obj_t * pObj, int iFrame )
{
    Aig_Obj_t * pObjNew, * pObjNew2, * pObjRepr, * pObjReprNew;
    // skip nodes without representative
    pObjRepr = Aig_ObjRepr(pAig, pObj);
    if ( pObjRepr == NULL )
        return;
    p->nConstrTotal++;
    assert( pObjRepr->Id < pObj->Id );
    // get the new node 
    pObjNew = Ssw_ObjFraig( p, pObj, iFrame );
    // get the new node of the representative
    pObjReprNew = Ssw_ObjFraig( p, pObjRepr, iFrame );
    // if this is the same node, no need to add constraints
    if ( pObj->fPhase == pObjRepr->fPhase )
    {
        assert( pObjNew != Aig_Not(pObjReprNew) );
        if ( pObjNew == pObjReprNew )
            return;
    }
    else
    {
        assert( pObjNew != pObjReprNew );
        if ( pObjNew == Aig_Not(pObjReprNew) )
            return;
    }
    p->nConstrReduced++;
    // these are different nodes - perform speculative reduction
    pObjNew2 = Aig_NotCond( pObjReprNew, pObj->fPhase ^ pObjRepr->fPhase );
    // set the new node
    Ssw_ObjSetFraig( p, pObj, iFrame, pObjNew2 );
    // add the constraint
    Aig_ObjCreatePo( pFrames, pObjNew2 );
    Aig_ObjCreatePo( pFrames, pObjNew );
}

/**Function*************************************************************

  Synopsis    [Prepares the inductive case with speculative reduction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Ssw_FramesWithClasses( Ssw_Man_t * p )
{
    Aig_Man_t * pFrames;
    Aig_Obj_t * pObj, * pObjLi, * pObjLo, * pObjNew;
    int i, f;
    assert( p->pFrames == NULL );
    assert( Aig_ManRegNum(p->pAig) > 0 );
    assert( Aig_ManRegNum(p->pAig) < Aig_ManPiNum(p->pAig) );

    // start the fraig package
    pFrames = Aig_ManStart( Aig_ManObjNumMax(p->pAig) * p->nFrames );
    // create latches for the first frame
    Saig_ManForEachLo( p->pAig, pObj, i )
        Ssw_ObjSetFraig( p, pObj, 0, Aig_ObjCreatePi(pFrames) );
    // add timeframes
    p->nConstrTotal = p->nConstrReduced = 0;
    for ( f = 0; f < p->pPars->nFramesK; f++ )
    {
        // map constants and PIs
        Ssw_ObjSetFraig( p, Aig_ManConst1(p->pAig), f, Aig_ManConst1(pFrames) );
        Aig_ManForEachPiSeq( p->pAig, pObj, i )
            Ssw_ObjSetFraig( p, pObj, f, Aig_ObjCreatePi(pFrames) );
        // set the constraints on the latch outputs
        Aig_ManForEachLoSeq( p->pAig, pObj, i )
            Ssw_FramesConstrainNode( p, pFrames, p->pAig, pObj, f );
        // add internal nodes of this frame
        Aig_ManForEachNode( p->pAig, pObj, i )
        {
            pObjNew = Aig_And( pFrames, Ssw_ObjChild0Fra(p, pObj, f), Ssw_ObjChild1Fra(p, pObj, f) );
            Ssw_ObjSetFraig( p, pObj, f, pObjNew );
            Ssw_FramesConstrainNode( p, pFrames, p->pAig, pObj, f );
        }
        // transfer latch input to the latch outputs 
        Saig_ManForEachLiLo( p->pAig, pObjLi, pObjLo, i )
            Ssw_ObjSetFraig( p, pObjLo, f+1, Ssw_ObjChild0Fra(p, pObjLi,f) );
    }
    // add the POs for the latch outputs of the last frame
    Saig_ManForEachLo( p->pAig, pObj, i )
        Aig_ObjCreatePo( pFrames, Ssw_ObjFraig( p, pObj, p->pPars->nFramesK ) );

    // remove dangling nodes
    Aig_ManCleanup( pFrames );
    // make sure the satisfying assignment is node assigned
    assert( pFrames->pData == NULL );
//Aig_ManShow( pFrames, 0, NULL );
    return pFrames;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


