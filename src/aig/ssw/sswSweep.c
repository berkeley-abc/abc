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

  Synopsis    [Mark nodes affected by sweep in the previous iteration.]

  Description [Assumes that affected nodes are in p->ppClasses->vRefined.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ManSweepMarkRefinement( Ssw_Man_t * p )
{
    Vec_Ptr_t * vRefined, * vSupp;
    Aig_Obj_t * pObj, * pObjLo, * pObjLi;
    int i, k;
    vRefined = Ssw_ClassesGetRefined( p->ppClasses );
    if ( Vec_PtrSize(vRefined) == 0 )
    {
        Aig_ManForEachObj( p->pAig, pObj, i )
            pObj->fMarkA = 1;
        return;
    }
    // mark the nodes to be refined
    Aig_ManCleanMarkA( p->pAig );
    Vec_PtrForEachEntry( vRefined, pObj, i )
    {
        if ( Aig_ObjIsPi(pObj) )
        {
            pObj->fMarkA = 1;
            continue;
        }
        assert( Aig_ObjIsNode(pObj) );
        vSupp = Aig_Support( p->pAig, pObj );
        Vec_PtrForEachEntry( vSupp, pObjLo, k )
            pObjLo->fMarkA = 1;
        Vec_PtrFree( vSupp );
    }
    // mark refinement
    Aig_ManForEachNode( p->pAig, pObj, i )
        pObj->fMarkA = Aig_ObjFanin0(pObj)->fMarkA | Aig_ObjFanin1(pObj)->fMarkA;
    Saig_ManForEachLi( p->pAig, pObj, i )
        pObj->fMarkA |= Aig_ObjFanin0(pObj)->fMarkA;
    Saig_ManForEachLiLo( p->pAig, pObjLi, pObjLo, i )
        pObjLo->fMarkA |= pObjLi->fMarkA;
}

/**Function*************************************************************

  Synopsis    [Retrives value of the PI in the original AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ssw_ManGetSatVarValue( Ssw_Man_t * p, Aig_Obj_t * pObj, int f )
{
    Aig_Obj_t * pObjFraig;
    int nVarNum, Value;
//    assert( Aig_ObjIsPi(pObj) );
    pObjFraig = Ssw_ObjFrame( p, pObj, f );
    nVarNum = Ssw_ObjSatNum( p, Aig_Regular(pObjFraig) );
    Value = (!nVarNum)? 0 : (Aig_IsComplement(pObjFraig) ^ sat_solver_var_value( p->pSat, nVarNum ));
//    Value = (Aig_IsComplement(pObjFraig) ^ ((!nVarNum)? 0 : sat_solver_var_value( p->pSat, nVarNum )));
//    Value = (!nVarNum)? Aig_ManRandom(0) & 1 : (Aig_IsComplement(pObjFraig) ^ sat_solver_var_value( p->pSat, nVarNum ));
    if ( p->pPars->fPolarFlip )
    {
        if ( Aig_Regular(pObjFraig)->fPhase )  Value ^= 1;
    }
    return Value;
}

/**Function*************************************************************

  Synopsis    [Copy pattern from the solver into the internal storage.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_SmlSavePatternAig( Ssw_Man_t * p, int f )
{
    Aig_Obj_t * pObj;
    int i;
    memset( p->pPatWords, 0, sizeof(unsigned) * p->nPatWords );
    Aig_ManForEachPi( p->pAig, pObj, i )
        if ( Ssw_ManGetSatVarValue( p, pObj, f ) )
            Aig_InfoSetBit( p->pPatWords, i );
}

/**Function*************************************************************

  Synopsis    [Copy pattern from the solver into the internal storage.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_SmlSavePatternAigPhase( Ssw_Man_t * p, int f )
{
    Aig_Obj_t * pObj;
    int i;
    memset( p->pPatWords, 0, sizeof(unsigned) * p->nPatWords );
    Aig_ManForEachPi( p->pAig, pObj, i )
        if ( Aig_ObjPhaseReal( Ssw_ObjFrame(p, pObj, f) ) )
            Aig_InfoSetBit( p->pPatWords, i );
}

/**Function*************************************************************

  Synopsis    [Performs fraiging for one node.]

  Description [Returns the fraiged node.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ssw_ManSweepNode( Ssw_Man_t * p, Aig_Obj_t * pObj, int f, int fBmc )
{ 
    Aig_Obj_t * pObjRepr, * pObjFraig, * pObjFraig2, * pObjReprFraig;
    int RetValue;
    // get representative of this class
    pObjRepr = Aig_ObjRepr( p->pAig, pObj );
    if ( pObjRepr == NULL )
        return 0;
    // get the fraiged node
    pObjFraig = Ssw_ObjFrame( p, pObj, f );
    // get the fraiged representative
    pObjReprFraig = Ssw_ObjFrame( p, pObjRepr, f );
    // check if constant 0 pattern distinquishes these nodes
    assert( pObjFraig != NULL && pObjReprFraig != NULL );
    if ( (pObj->fPhase == pObjRepr->fPhase) != (Aig_ObjPhaseReal(pObjFraig) == Aig_ObjPhaseReal(pObjReprFraig)) )
    {
        p->nStrangers++;
        Ssw_SmlSavePatternAigPhase( p, f );
    }
    else
    { 
        // if the fraiged nodes are the same, return
        if ( Aig_Regular(pObjFraig) == Aig_Regular(pObjReprFraig) )
            return 0; 
        // count the number of skipped calls
        if ( !pObj->fMarkA && !pObjRepr->fMarkA )
            p->nRefSkip++;
        else
            p->nRefUse++;
        // call equivalence checking
        if ( p->pPars->fSkipCheck && !fBmc && !pObj->fMarkA && !pObjRepr->fMarkA )
            RetValue = 1;
        else if ( Aig_Regular(pObjFraig) != Aig_ManConst1(p->pFrames) )
            RetValue = Ssw_NodesAreEquiv( p, Aig_Regular(pObjReprFraig), Aig_Regular(pObjFraig) );
        else
            RetValue = Ssw_NodesAreEquiv( p, Aig_Regular(pObjFraig), Aig_Regular(pObjReprFraig) );
        if ( RetValue == 1 )  // proved equivalent
        {
            pObjFraig2 = Aig_NotCond( pObjReprFraig, pObj->fPhase ^ pObjRepr->fPhase );
            Ssw_ObjSetFrame( p, pObj, f, pObjFraig2 );
            return 0;
        }
        if ( RetValue == -1 ) // timed out
        {
            Ssw_ClassesRemoveNode( p->ppClasses, pObj );
            return 1;
        }
        // check if skipping calls works correctly
        if ( p->pPars->fSkipCheck && !fBmc && !pObj->fMarkA && !pObjRepr->fMarkA )
        {
            assert( 0 );
            printf( "\nSsw_ManSweepNode(): Error!\n" );
        }
        // disproved the equivalence
        Ssw_SmlSavePatternAig( p, f );
    }
    if ( !fBmc && p->pPars->fUniqueness && p->pPars->nFramesK > 1 && 
        Ssw_ManUniqueOne( p, pObjRepr, pObj ) && p->iOutputLit == -1 )
    {
        if ( Ssw_ManUniqueAddConstraint( p, p->vCommon, 0, 1 ) )
        {
            int RetValue;
            assert( p->iOutputLit > -1 );
            RetValue = Ssw_ManSweepNode( p, pObj, f, 0 );
            p->iOutputLit = -1;
            return RetValue;
        }
    }
    if ( p->pPars->nConstrs == 0 )
        Ssw_ManResimulateWord( p, pObj, pObjRepr, f );
    else
        Ssw_ManResimulateBit( p, pObj, pObjRepr );
    assert( Aig_ObjRepr( p->pAig, pObj ) != pObjRepr );
    return 1;
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
    Aig_Obj_t * pObj, * pObjNew, * pObjLi, * pObjLo;
    int i, f, clk;
clk = clock();

    // start initialized timeframes
    p->pFrames = Aig_ManStart( Aig_ManObjNumMax(p->pAig) * p->pPars->nFramesK );
    Saig_ManForEachLo( p->pAig, pObj, i )
        Ssw_ObjSetFrame( p, pObj, 0, Aig_ManConst0(p->pFrames) );

    // sweep internal nodes
    p->fRefined = 0;
    if ( p->pPars->fVerbose )
        pProgress = Bar_ProgressStart( stdout, Aig_ManObjNumMax(p->pAig) * p->pPars->nFramesK );
    Ssw_ManStartSolver( p );
    for ( f = 0; f < p->pPars->nFramesK; f++ )
    {
        // map constants and PIs
        Ssw_ObjSetFrame( p, Aig_ManConst1(p->pAig), f, Aig_ManConst1(p->pFrames) );
        Saig_ManForEachPi( p->pAig, pObj, i )
            Ssw_ObjSetFrame( p, pObj, f, Aig_ObjCreatePi(p->pFrames) );
        // sweep internal nodes
        Aig_ManForEachNode( p->pAig, pObj, i )
        {
            if ( p->pPars->fVerbose )
                Bar_ProgressUpdate( pProgress, Aig_ManObjNumMax(p->pAig) * f + i, NULL );
            pObjNew = Aig_And( p->pFrames, Ssw_ObjChild0Fra(p, pObj, f), Ssw_ObjChild1Fra(p, pObj, f) );
            Ssw_ObjSetFrame( p, pObj, f, pObjNew );
            p->fRefined |= Ssw_ManSweepNode( p, pObj, f, 1 );
        }
        // quit if this is the last timeframe
        if ( f == p->pPars->nFramesK - 1 )
            break;
        // transfer latch input to the latch outputs 
        // build logic cones for register outputs
        Saig_ManForEachLiLo( p->pAig, pObjLi, pObjLo, i )
        {
            pObjNew = Ssw_ObjChild0Fra(p, pObjLi,f);
            Ssw_ObjSetFrame( p, pObjLo, f+1, pObjNew );
            Ssw_CnfNodeAddToSolver( p, Aig_Regular(pObjNew) );
        }
    }
    if ( p->pPars->fVerbose )
        Bar_ProgressStop( pProgress );

    // cleanup
//    Ssw_ClassesCheck( p->ppClasses );
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
    int nConstrPairs, clk, i, f;
    int v;

    // perform speculative reduction
clk = clock();
    // create timeframes
    p->pFrames = Ssw_FramesWithClasses( p );
    // add constraints
    Ssw_ManStartSolver( p );
    nConstrPairs = Aig_ManPoNum(p->pFrames)-Aig_ManRegNum(p->pAig);
    assert( (nConstrPairs & 1) == 0 );
    for ( i = 0; i < nConstrPairs; i += 2 )
    {
        pObj  = Aig_ManPo( p->pFrames, i   );
        pObj2 = Aig_ManPo( p->pFrames, i+1 );
        Ssw_NodesAreConstrained( p, Aig_ObjChild0(pObj), Aig_ObjChild0(pObj2) );
    }
    // build logic cones for register inputs
    for ( i = 0; i < Aig_ManRegNum(p->pAig); i++ )
    {
        pObj  = Aig_ManPo( p->pFrames, nConstrPairs + i );
        Ssw_CnfNodeAddToSolver( p, Aig_ObjFanin0(pObj) );
    }
    sat_solver_simplify( p->pSat );
p->timeReduce += clock() - clk;

    // mark nodes that do not have to be refined
clk = clock();
    if ( p->pPars->fSkipCheck )
        Ssw_ManSweepMarkRefinement( p );
p->timeMarkCones += clock() - clk;

//Ssw_ManUnique( p );

    // map constants and PIs of the last frame
    f = p->pPars->nFramesK;
    Ssw_ObjSetFrame( p, Aig_ManConst1(p->pAig), f, Aig_ManConst1(p->pFrames) );
    Saig_ManForEachPi( p->pAig, pObj, i )
        Ssw_ObjSetFrame( p, pObj, f, Aig_ObjCreatePi(p->pFrames) );
    // make sure LOs are assigned
    Saig_ManForEachLo( p->pAig, pObj, i )
        assert( Ssw_ObjFrame( p, pObj, f ) != NULL );
////    
    // bring up the previous frames
    if ( p->pPars->fUniqueness )
        for ( v = 0; v < f; v++ )
            Saig_ManForEachLo( p->pAig, pObj, i )
                Ssw_CnfNodeAddToSolver( p, Aig_Regular(Ssw_ObjFrame(p, pObj, v)) );
////
    // sweep internal nodes
    p->fRefined = 0;
    p->nSatFailsReal = 0;
    p->nRefUse = p->nRefSkip = 0;
    p->nUniques = 0;
    Ssw_ClassesClearRefined( p->ppClasses );
    if ( p->pPars->fVerbose )
        pProgress = Bar_ProgressStart( stdout, Aig_ManObjNumMax(p->pAig) );
    Aig_ManForEachObj( p->pAig, pObj, i )
    {
        if ( p->pPars->fVerbose )
            Bar_ProgressUpdate( pProgress, i, NULL );
        if ( Saig_ObjIsLo(p->pAig, pObj) )
            p->fRefined |= Ssw_ManSweepNode( p, pObj, f, 0 );
        else if ( Aig_ObjIsNode(pObj) )
        { 
            pObj->fMarkA = Aig_ObjFanin0(pObj)->fMarkA | Aig_ObjFanin1(pObj)->fMarkA;
            pObjNew = Aig_And( p->pFrames, Ssw_ObjChild0Fra(p, pObj, f), Ssw_ObjChild1Fra(p, pObj, f) );
            Ssw_ObjSetFrame( p, pObj, f, pObjNew );
            p->fRefined |= Ssw_ManSweepNode( p, pObj, f, 0 );
        }
    }
    p->nSatFailsTotal += p->nSatFailsReal;
    if ( p->pPars->fVerbose )
        Bar_ProgressStop( pProgress );

    // cleanup
//    Ssw_ClassesCheck( p->ppClasses );
    return p->fRefined;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


