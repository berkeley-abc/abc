/**CFile****************************************************************

  FileName    [fraInd.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New FRAIG package.]

  Synopsis    [Inductive prover.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 30, 2007.]

  Revision    [$Id: fraInd.c,v 1.00 2007/06/30 00:00:00 alanmi Exp $]

***********************************************************************/

#include "fra.h"
#include "cnf.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Prepares the inductive case with speculative reduction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Fra_FramesWithClasses( Fra_Man_t * p )
{
    Aig_Man_t * pManFraig;
    Aig_Obj_t * pObj, * pObjRepr, * pObjNew, * pObjReprNew, * pMiter;
    Aig_Obj_t ** pLatches;
    int i, k, f;
    assert( p->pManFraig == NULL );
    assert( Aig_ManInitNum(p->pManAig) > 0 );
    assert( Aig_ManInitNum(p->pManAig) < Aig_ManPiNum(p->pManAig) );

    // start the fraig package
    pManFraig = Aig_ManStart( (Aig_ManObjIdMax(p->pManAig) + 1) * p->nFrames );
    pManFraig->vInits = Vec_IntDup(p->pManAig->vInits);
    // create PI nodes for the frames
    for ( f = 0; f < p->nFrames; f++ )
    {
        Fra_ObjSetFraig( Aig_ManConst1(p->pManAig), f, Aig_ManConst1(pManFraig) );
        Aig_ManForEachPiSeq( p->pManAig, pObj, i )
            Fra_ObjSetFraig( pObj, f, Aig_ObjCreatePi(pManFraig) );
    }
    // create latches for the first frame
    Aig_ManForEachLoSeq( p->pManAig, pObj, i )
        Fra_ObjSetFraig( pObj, 0, Aig_ObjCreatePi(pManFraig) );

    // add timeframes
    pLatches = ALLOC( Aig_Obj_t *, Aig_ManInitNum(p->pManAig) );
    for ( f = 0; f < p->nFrames - 1; f++ )
    {
        // add internal nodes of this frame
        Aig_ManForEachNode( p->pManAig, pObj, i )
        {
            pObjNew = Aig_And( pManFraig, Fra_ObjChild0Fra(pObj,f), Fra_ObjChild1Fra(pObj,f) );
            Fra_ObjSetFraig( pObj, f, pObjNew );
            // skip nodes without representative
            if ( (pObjRepr = Fra_ClassObjRepr(pObj)) == NULL )
                continue;
            assert( pObjRepr->Id < pObj->Id );
            // get the new node of the representative
            pObjReprNew = Fra_ObjFraig( pObjRepr, f );
            // if this is the same node, no need to add constraints
            if ( Aig_Regular(pObjNew) == Aig_Regular(pObjReprNew) )
                continue;
            // these are different nodes
            // perform speculative reduction
            Fra_ObjSetFraig( pObj, f, Aig_NotCond(pObjReprNew, pObj->fPhase ^ pObjRepr->fPhase) );
            // add the constraint
            pMiter = Aig_Exor( pManFraig, pObjNew, pObjReprNew );
            pMiter = Aig_NotCond( pMiter, Aig_Regular(pMiter)->fPhase ^ Aig_IsComplement(pMiter) );
            Aig_ObjCreatePo( pManFraig, pMiter );
        }
        // save the latch input values
        k = 0;
        Aig_ManForEachLiSeq( p->pManAig, pObj, i )
            pLatches[k++] = Fra_ObjChild0Fra(pObj,f);
        assert( k == Aig_ManInitNum(p->pManAig) );
        // insert them to the latch output values
        k = 0;
        Aig_ManForEachLoSeq( p->pManAig, pObj, i )
            Fra_ObjSetFraig( pObj, f+1, pLatches[k++] );
        assert( k == Aig_ManInitNum(p->pManAig) );
    }
    free( pLatches );
    // mark the asserts
    pManFraig->nAsserts = Aig_ManPoNum(pManFraig);
    // add the POs for the latch inputs
    Aig_ManForEachLiSeq( p->pManAig, pObj, i )
        Aig_ObjCreatePo( pManFraig, Fra_ObjChild0Fra(pObj,f) );

    // set the pointer to the manager
    Aig_ManForEachObj( p->pManAig, pObj, i )
        pObj->pData = p;
    // set the pointers to the manager
    Aig_ManForEachObj( pManFraig, pObj, i )
        pObj->pData = p;
    // make sure the satisfying assignment is node assigned
    assert( pManFraig->pData == NULL );
    return pManFraig;
}

/**Function*************************************************************

  Synopsis    [Performs choicing of the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Fra_Induction( Aig_Man_t * pManAig, int nFrames, int fVerbose )
{
    Fra_Man_t * p;
    Fra_Par_t Pars, * pPars = &Pars; 
    Aig_Obj_t * pObj;
    Cnf_Dat_t * pCnf;
    Aig_Man_t * pManAigNew;
    int nIter, i;

    if ( Aig_ManNodeNum(pManAig) == 0 )
        return Aig_ManDup(pManAig, 1);
    assert( Aig_ManLatchNum(pManAig) == 0 );
    assert( Aig_ManInitNum(pManAig) > 0 );

    // get parameters
    Fra_ParamsDefaultSeq( pPars );
    pPars->nTimeFrames = nFrames;
    pPars->fVerbose = fVerbose;

    // start the fraig manager for this run
    p = Fra_ManStart( pManAig, pPars );
    // derive and refine e-classes using the 1st init frame
    Fra_Simulate( p, 1 );

    // refine e-classes using sequential simulation

    // iterate the inductive case
    p->pCla->fRefinement = 1;
    for ( nIter = 0; p->pCla->fRefinement; nIter++ )
    {
        // mark the classes as non-refined
        p->pCla->fRefinement = 0;
        // derive non-init K-timeframes while implementing e-classes
        p->pManFraig = Fra_FramesWithClasses( p );
        if ( fVerbose )
            printf( "Iter = %3d.  Original = %6d. Reduced = %6d.\n", 
                nIter, Fra_ClassesCountLits(p->pCla), p->pManFraig->nAsserts );

        // perform AIG rewriting on the speculated frames

        // convert the manager to SAT solver (the last nLatches outputs are inputs)
        pCnf = Cnf_Derive( p->pManFraig, Aig_ManInitNum(p->pManFraig) );
        p->pSat = Cnf_DataWriteIntoSolver( pCnf );
        // transfer variable numbers
        Aig_ManForEachPi( p->pManAig, pObj, i )
            Fra_ObjSetSatNum( pObj, pCnf->pVarNums[pObj->Id] );
        Aig_ManForEachLiSeq( p->pManAig, pObj, i )
        {
            Fra_ObjSetSatNum( pObj, pCnf->pVarNums[pObj->Id] );
            Fra_ObjSetFaninVec( pObj, (void *)1 );
        }
        Cnf_DataFree( pCnf );

        // perform sweeping
        Fra_FraigSweep( p );
        assert( Vec_PtrSize(p->vTimeouts) == 0 );
        Aig_ManStop( p->pManFraig );   p->pManFraig = NULL;
        sat_solver_delete( p->pSat );  p->pSat = NULL;
    }

    // move the classes into representatives
    Fra_ClassesCopyReprs( p->pCla, p->vTimeouts );
    // implement the classes
    pManAigNew = Aig_ManDupRepr( pManAig );
    Fra_ManStop( p );
    return pManAigNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


