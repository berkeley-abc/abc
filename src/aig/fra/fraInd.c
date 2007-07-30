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

  Synopsis    [Performs speculative reduction for one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Fra_FramesConstrainNode( Aig_Man_t * pManFraig, Aig_Obj_t * pObj, int iFrame )
{
    Aig_Obj_t * pObjNew, * pObjNew2, * pObjRepr, * pObjReprNew, * pMiter;
    // skip nodes without representative
    if ( (pObjRepr = Fra_ClassObjRepr(pObj)) == NULL )
        return;
    assert( pObjRepr->Id < pObj->Id );
    // get the new node 
    pObjNew = Fra_ObjFraig( pObj, iFrame );
    // get the new node of the representative
    pObjReprNew = Fra_ObjFraig( pObjRepr, iFrame );
    // if this is the same node, no need to add constraints
    if ( Aig_Regular(pObjNew) == Aig_Regular(pObjReprNew) )
        return;
    // these are different nodes - perform speculative reduction
    pObjNew2 = Aig_NotCond( pObjReprNew, pObj->fPhase ^ pObjRepr->fPhase );
    // set the new node
    Fra_ObjSetFraig( pObj, iFrame, pObjNew2 );
    // add the constraint
    pMiter = Aig_Exor( pManFraig, Aig_Regular(pObjNew), Aig_Regular(pObjReprNew) );
    pMiter = Aig_NotCond( pMiter, Aig_Regular(pMiter)->fPhase ^ Aig_IsComplement(pMiter) );
    pMiter = Aig_Not( pMiter );
    Aig_ObjCreatePo( pManFraig, pMiter );
}

/**Function*************************************************************

  Synopsis    [Prepares the inductive case with speculative reduction.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Fra_FramesWithClasses( Fra_Man_t * p )
{
    Aig_Man_t * pManFraig;
    Aig_Obj_t * pObj, * pObjNew;
    Aig_Obj_t ** pLatches;
    int i, k, f;
    assert( p->pManFraig == NULL );
    assert( Aig_ManRegNum(p->pManAig) > 0 );
    assert( Aig_ManRegNum(p->pManAig) < Aig_ManPiNum(p->pManAig) );

    // start the fraig package
    pManFraig = Aig_ManStart( (Aig_ManObjIdMax(p->pManAig) + 1) * p->nFramesAll );
    pManFraig->nRegs = p->pManAig->nRegs;
    // create PI nodes for the frames
    for ( f = 0; f < p->nFramesAll; f++ )
        Fra_ObjSetFraig( Aig_ManConst1(p->pManAig), f, Aig_ManConst1(pManFraig) );
    for ( f = 0; f < p->nFramesAll; f++ )
        Aig_ManForEachPiSeq( p->pManAig, pObj, i )
            Fra_ObjSetFraig( pObj, f, Aig_ObjCreatePi(pManFraig) );
    // create latches for the first frame
    Aig_ManForEachLoSeq( p->pManAig, pObj, i )
        Fra_ObjSetFraig( pObj, 0, Aig_ObjCreatePi(pManFraig) );

    // add timeframes
    pLatches = ALLOC( Aig_Obj_t *, Aig_ManRegNum(p->pManAig) );
    for ( f = 0; f < p->nFramesAll - 1; f++ )
    {
        // set the constraints on the latch outputs
        Aig_ManForEachLoSeq( p->pManAig, pObj, i )
            Fra_FramesConstrainNode( pManFraig, pObj, f );
        // add internal nodes of this frame
        Aig_ManForEachNode( p->pManAig, pObj, i )
        {
            pObjNew = Aig_And( pManFraig, Fra_ObjChild0Fra(pObj,f), Fra_ObjChild1Fra(pObj,f) );
            Fra_ObjSetFraig( pObj, f, pObjNew );
            Fra_FramesConstrainNode( pManFraig, pObj, f );
        }
        // save the latch input values
        k = 0;
        Aig_ManForEachLiSeq( p->pManAig, pObj, i )
            pLatches[k++] = Fra_ObjChild0Fra(pObj,f);
        assert( k == Aig_ManRegNum(p->pManAig) );
        // insert them to the latch output values
        k = 0;
        Aig_ManForEachLoSeq( p->pManAig, pObj, i )
            Fra_ObjSetFraig( pObj, f+1, pLatches[k++] );
        assert( k == Aig_ManRegNum(p->pManAig) );
    }
    free( pLatches );
    // mark the asserts
    pManFraig->nAsserts = Aig_ManPoNum(pManFraig);
    // add the POs for the latch inputs
    Aig_ManForEachLiSeq( p->pManAig, pObj, i )
        Aig_ObjCreatePo( pManFraig, Fra_ObjChild0Fra(pObj,f-1) );

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
Aig_Man_t * Fra_FraigInduction( Aig_Man_t * pManAig, int nFramesK, int fVerbose )
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
    assert( Aig_ManRegNum(pManAig) > 0 );
    assert( nFramesK > 0 );

    // get parameters
    Fra_ParamsDefaultSeq( pPars );
    pPars->nFramesK = nFramesK;
    pPars->fVerbose = fVerbose;

    // start the fraig manager for this run
    p = Fra_ManStart( pManAig, pPars );
    // derive and refine e-classes using the 1st init frame
    Fra_Simulate( p, 1 );
//    Fra_ClassesTest( p->pCla, 2, 3 );
//Aig_ManShow( pManAig, 0, NULL );

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
        {
            printf( "%3d : Const = %6d. Class = %6d.  L = %6d. LR = %6d.  N = %6d. NR = %6d.\n", 
                nIter, Vec_PtrSize(p->pCla->vClasses1), Vec_PtrSize(p->pCla->vClasses), 
                Fra_ClassesCountLits(p->pCla), p->pManFraig->nAsserts,
                Aig_ManNodeNum(p->pManAig), Aig_ManNodeNum(p->pManFraig) );
        }
        // perform AIG rewriting on the speculated frames

        // convert the manager to SAT solver (the last nLatches outputs are inputs)
//        pCnf = Cnf_Derive( p->pManFraig, Aig_ManRegNum(p->pManFraig) );
        pCnf = Cnf_DeriveSimple( p->pManFraig, Aig_ManRegNum(p->pManFraig) );
//Cnf_DataWriteIntoFile( pCnf, "temp.cnf", 1 );

        p->pSat = Cnf_DataWriteIntoSolver( pCnf );
        p->nSatVars = pCnf->nVars;

        // set the pointers to the manager
        Aig_ManForEachObj( p->pManFraig, pObj, i )
            pObj->pData = p;
        // transfer PI/LO variable numbers
        pObj = Aig_ManConst1( p->pManFraig );
        Fra_ObjSetSatNum( pObj, pCnf->pVarNums[pObj->Id] );
        Aig_ManForEachPi( p->pManFraig, pObj, i )
            Fra_ObjSetSatNum( pObj, pCnf->pVarNums[pObj->Id] );
        // transfer LI variable numbers
        Aig_ManForEachLiSeq( p->pManFraig, pObj, i )
        {
            Fra_ObjSetSatNum( pObj, pCnf->pVarNums[pObj->Id] );
            Fra_ObjSetFaninVec( pObj, (void *)1 );
        }
        Cnf_DataFree( pCnf );

        // perform sweeping
        Fra_FraigSweep( p );
        assert( p->vTimeouts == NULL );

        // cleanup
        Fra_ManClean( p );
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


