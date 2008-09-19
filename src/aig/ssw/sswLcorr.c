/**CFile****************************************************************

  FileName    [sswLcorr.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Inductive prover with constraints.]

  Synopsis    [Latch correspondence.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 1, 2008.]

  Revision    [$Id: sswLcorr.c,v 1.00 2008/09/01 00:00:00 alanmi Exp $]

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

  Synopsis    [Recycles the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ManSatSolverRecycle( Ssw_Man_t * p )
{
    int Lit;
    if ( p->pSat )
    {
        Aig_Obj_t * pObj;
        int i;
        Vec_PtrForEachEntry( p->vUsedNodes, pObj, i )
            Ssw_ObjSetSatNum( p, pObj, 0 );
        Vec_PtrClear( p->vUsedNodes );
        Vec_PtrClear( p->vUsedPis );
//        memset( p->pSatVars, 0, sizeof(int) * Aig_ManObjNumMax(p->pAigTotal) );
        sat_solver_delete( p->pSat );
    }
    p->pSat = sat_solver_new();
    sat_solver_setnvars( p->pSat, 1000 );
    // var 0 is not used
    // var 1 is reserved for const1 node - add the clause
    p->nSatVars = 1;
//    p->nSatVars = 0;
    Lit = toLit( p->nSatVars );
    if ( p->pPars->fPolarFlip )
        Lit = lit_neg( Lit );
    sat_solver_addclause( p->pSat, &Lit, &Lit + 1 );
    Ssw_ObjSetSatNum( p, Aig_ManConst1(p->pFrames), p->nSatVars++ );

    p->nRecycles++;
    p->nCallsSince = 0;
}

/**Function*************************************************************

  Synopsis    [Copy pattern from the solver into the internal storage.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_SmlSavePatternLatch( Ssw_Man_t * p )
{
    Aig_Obj_t * pObj;
    int i;
    memset( p->pPatWords, 0, sizeof(unsigned) * p->nPatWords );
    Aig_ManForEachPi( p->pAig, pObj, i )
        if ( Ssw_ManOriginalPiValue( p, pObj, 0 ) )
            Aig_InfoSetBit( p->pPatWords, i );
}

/**Function*************************************************************

  Synopsis    [Copy pattern from the solver into the internal storage.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_SmlSavePatternLatchPhase( Ssw_Man_t * p, int f )
{
    Aig_Obj_t * pObj;
    int i;
    memset( p->pPatWords, 0, sizeof(unsigned) * p->nPatWords );
    Aig_ManForEachPi( p->pAig, pObj, i )
        if ( Aig_ObjPhaseReal( Ssw_ObjFraig(p, pObj, f) ) )
            Aig_InfoSetBit( p->pPatWords, i );
}

/**Function*************************************************************

  Synopsis    [Builds fraiged logic cone of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ManBuildCone_rec( Ssw_Man_t * p, Aig_Obj_t * pObj )
{
    Aig_Obj_t * pObjNew;
    assert( !Aig_IsComplement(pObj) );
    if ( Ssw_ObjFraig( p, pObj, 0 ) )
        return;
    assert( Aig_ObjIsNode(pObj) );
    Ssw_ManBuildCone_rec( p, Aig_ObjFanin0(pObj) );
    Ssw_ManBuildCone_rec( p, Aig_ObjFanin1(pObj) );
    pObjNew = Aig_And( p->pFrames, Ssw_ObjChild0Fra(p, pObj, 0), Ssw_ObjChild1Fra(p, pObj, 0) );
    Ssw_ObjSetFraig( p, pObj, 0, pObjNew );
}

/**Function*************************************************************

  Synopsis    [Recycles the SAT solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ManSweepLatchOne( Ssw_Man_t * p, Aig_Obj_t * pObjRepr, Aig_Obj_t * pObj )
{
    Aig_Obj_t * pObjFraig, * pObjFraig2, * pObjReprFraig, * pObjLi;
    int RetValue;
    assert( Aig_ObjIsPi(pObj) );
    assert( Aig_ObjIsPi(pObjRepr) || Aig_ObjIsConst1(pObjRepr) );
    // get the fraiged node
    pObjLi = Saig_ObjLoToLi( p->pAig, pObj ); 
    Ssw_ManBuildCone_rec( p, Aig_ObjFanin0(pObjLi) );
    pObjFraig = Ssw_ObjChild0Fra( p, pObjLi, 0 );
    // get the fraiged representative
    if ( Aig_ObjIsPi(pObjRepr) )
    {
        pObjLi = Saig_ObjLoToLi( p->pAig, pObjRepr ); 
        Ssw_ManBuildCone_rec( p, Aig_ObjFanin0(pObjLi) );
        pObjReprFraig = Ssw_ObjChild0Fra( p, pObjLi, 0 );
    }
    else 
        pObjReprFraig = Ssw_ObjFraig( p, pObjRepr, 0 );
    // if the fraiged nodes are the same, return
    if ( Aig_Regular(pObjFraig) == Aig_Regular(pObjReprFraig) )
        return;
    p->nCallsSince++;
    // check equivalence of the two nodes
    if ( (pObj->fPhase == pObjRepr->fPhase) != (Aig_ObjPhaseReal(pObjFraig) == Aig_ObjPhaseReal(pObjReprFraig)) )
    {
        p->nStrangers++;
        Ssw_SmlSavePatternLatchPhase( p, 0 );
    }
    else
    { 
        RetValue = Ssw_NodesAreEquiv( p, Aig_Regular(pObjReprFraig), Aig_Regular(pObjFraig) );
        if ( RetValue == 1 )  // proved equivalent
        {
            pObjFraig2 = Aig_NotCond( pObjReprFraig, pObj->fPhase ^ pObjRepr->fPhase );
            Ssw_ObjSetFraig( p, pObj, 0, pObjFraig2 );
            return;
        }
        else if ( RetValue == -1 ) // timed out
        {
            Ssw_ClassesRemoveNode( p->ppClasses, pObj );
            p->fRefined = 1;
            return;
        }
        else // disproved the equivalence
        {       
            Ssw_SmlSavePatternLatch( p );
        }
    }
    if ( p->pPars->nConstrs == 0 )
        Ssw_ManResimulateCexTotalSim( p, pObj, pObjRepr, 0 );
    else
        Ssw_ManResimulateCexTotal( p, pObj, pObjRepr, 0 );
    assert( Aig_ObjRepr( p->pAig, pObj ) != pObjRepr );
    p->fRefined = 1;
}

/**Function*************************************************************

  Synopsis    [Performs one iteration of sweeping latches.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ssw_ManSweepLatch( Ssw_Man_t * p )
{
    Bar_Progress_t * pProgress = NULL;
    Vec_Ptr_t * vClass;
    Aig_Obj_t * pObj, * pRepr, * pTemp;
    int i, k;

    // start the timeframe
    p->pFrames = Aig_ManStart( Aig_ManObjNumMax(p->pAig) );
    // map constants and PIs
    Ssw_ObjSetFraig( p, Aig_ManConst1(p->pAig), 0, Aig_ManConst1(p->pFrames) );
    Saig_ManForEachPi( p->pAig, pObj, i )
        Ssw_ObjSetFraig( p, pObj, 0, Aig_ObjCreatePi(p->pFrames) );

    // implement equivalence classes
    Saig_ManForEachLo( p->pAig, pObj, i )
    {
        pRepr = Aig_ObjRepr( p->pAig, pObj );
        if ( pRepr == NULL )
            pTemp = Aig_ObjCreatePi(p->pFrames);
        else
            pTemp = Aig_NotCond( Ssw_ObjFraig(p, pRepr, 0), pRepr->fPhase ^ pObj->fPhase );
        Ssw_ObjSetFraig( p, pObj, 0, pTemp );
    }

    // go through the registers
    if ( p->pPars->fVerbose )
        pProgress = Bar_ProgressStart( stdout, Aig_ManRegNum(p->pAig) );
    vClass = Vec_PtrAlloc( 100 );
    p->fRefined = 0;
    Saig_ManForEachLo( p->pAig, pObj, i )
    {
        if ( p->pPars->fVerbose )
            Bar_ProgressUpdate( pProgress, i, NULL );
        // consider the case of constant candidate
        if ( Ssw_ObjIsConst1Cand( p->pAig, pObj ) )
            Ssw_ManSweepLatchOne( p, Aig_ManConst1(p->pAig), pObj );
        else
        {
            // consider the case of equivalence class
            Ssw_ClassesCollectClass( p->ppClasses, pObj, vClass );
            if ( Vec_PtrSize(vClass) == 0 )
                continue;
            // try to prove equivalences in this class
            Vec_PtrForEachEntry( vClass, pTemp, k )
                if ( Aig_ObjRepr(p->pAig, pTemp) == pObj )
                    Ssw_ManSweepLatchOne( p, pObj, pTemp );
        }
        // attempt recycling the SAT solver
        if ( p->pPars->nSatVarMax && 
             p->nSatVars > p->pPars->nSatVarMax &&
             p->nCallsSince > p->pPars->nCallsRecycle )
             Ssw_ManSatSolverRecycle( p );
    }
    Vec_PtrFree( vClass );
    p->nSatFailsTotal += p->nSatFailsReal;
    if ( p->pPars->fVerbose )
        Bar_ProgressStop( pProgress );

    // cleanup
    Ssw_ClassesCheck( p->ppClasses );
    return p->fRefined;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


