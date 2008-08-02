/**CFile****************************************************************

  FileName    [dchSat.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Choice computation for tech-mapping.]

  Synopsis    [Calls to the SAT solver.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 29, 2008.]

  Revision    [$Id: dchSat.c,v 1.00 2008/07/29 00:00:00 alanmi Exp $]

***********************************************************************/

#include "dchInt.h"
#include "bar.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static inline Aig_Obj_t * Dch_ObjFraig( Aig_Obj_t * pObj )                       { return pObj->pData;  }
static inline void        Dch_ObjSetFraig( Aig_Obj_t * pObj, Aig_Obj_t * pNode ) { pObj->pData = pNode; }

static inline Aig_Obj_t * Dch_ObjChild0Fra( Aig_Obj_t * pObj ) { assert( !Aig_IsComplement(pObj) ); return Aig_ObjFanin0(pObj)? Aig_NotCond(Dch_ObjFraig(Aig_ObjFanin0(pObj)), Aig_ObjFaninC0(pObj)) : NULL;  }
static inline Aig_Obj_t * Dch_ObjChild1Fra( Aig_Obj_t * pObj ) { assert( !Aig_IsComplement(pObj) ); return Aig_ObjFanin1(pObj)? Aig_NotCond(Dch_ObjFraig(Aig_ObjFanin1(pObj)), Aig_ObjFaninC1(pObj)) : NULL;  }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns 1 if the node appears to be constant 1 candidate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dch_NodeIsConstCex( void * p, Aig_Obj_t * pObj )
{
    return pObj->fPhase == pObj->fMarkB;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if the nodes appear equal.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Dch_NodesAreEqualCex( void * p, Aig_Obj_t * pObj0, Aig_Obj_t * pObj1 )
{
    return (pObj0->fPhase == pObj1->fPhase) == (pObj0->fMarkB == pObj1->fMarkB);
}

/**Function*************************************************************

  Synopsis    [Resimulates the cone of influence of the solved nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dch_ManResimulateSolved_rec( Dch_Man_t * p, Aig_Obj_t * pObj )
{
    if ( Aig_ObjIsTravIdCurrent(p->pAigTotal, pObj) )
        return;
    Aig_ObjSetTravIdCurrent(p->pAigTotal, pObj);
    if ( Aig_ObjIsPi(pObj) )
    {
        // get the value from the SAT solver
        assert( p->pSatVars[pObj->Id] > 0 );
        pObj->fMarkB = sat_solver_var_value( p->pSat, p->pSatVars[pObj->Id] );
        return;
    }
    Dch_ManResimulateSolved_rec( p, Aig_ObjFanin0(pObj) );
    Dch_ManResimulateSolved_rec( p, Aig_ObjFanin1(pObj) );
    pObj->fMarkB = ( Aig_ObjFanin0(pObj)->fMarkB ^ Aig_ObjFaninC0(pObj) )
                 & ( Aig_ObjFanin1(pObj)->fMarkB ^ Aig_ObjFaninC1(pObj) );
    // count the cone size
    if ( Dch_ObjSatNum( p, Aig_Regular(Dch_ObjFraig(pObj)) ) > 0 )
        p->nConeThis++;
}

/**Function*************************************************************

  Synopsis    [Resimulates the cone of influence of the other nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dch_ManResimulateOther_rec( Dch_Man_t * p, Aig_Obj_t * pObj )
{
    if ( Aig_ObjIsTravIdCurrent(p->pAigTotal, pObj) )
        return;
    Aig_ObjSetTravIdCurrent(p->pAigTotal, pObj);
    if ( Aig_ObjIsPi(pObj) )
    {
        // set random value
        pObj->fMarkB = Aig_ManRandom(0) & 1;
        return;
    }
    Dch_ManResimulateOther_rec( p, Aig_ObjFanin0(pObj) );
    Dch_ManResimulateOther_rec( p, Aig_ObjFanin1(pObj) );
    pObj->fMarkB = ( Aig_ObjFanin0(pObj)->fMarkB ^ Aig_ObjFaninC0(pObj) )
                 & ( Aig_ObjFanin1(pObj)->fMarkB ^ Aig_ObjFaninC1(pObj) );
}

/**Function*************************************************************

  Synopsis    [Handle the counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dch_ManSweepResimulate( Dch_Man_t * p, Aig_Obj_t * pObj, Aig_Obj_t * pRepr )
{
    Aig_Obj_t * pRoot;
    int i, RetValue, clk = clock();
    // get the equivalence class
    if ( Dch_ObjIsConst1Cand(p->pAigTotal, pObj) )
        Dch_ClassesCollectConst1Group( p->ppClasses, pObj, 500, p->vRoots );
    else
        Dch_ClassesCollectOneClass( p->ppClasses, pRepr, p->vRoots );
    // resimulate the cone of influence of the solved nodes
    p->nConeThis = 0;
    Aig_ManIncrementTravId( p->pAigTotal );
    Aig_ObjSetTravIdCurrent( p->pAigTotal, Aig_ManConst1(p->pAigTotal) );
    Dch_ManResimulateSolved_rec( p, pObj );
    Dch_ManResimulateSolved_rec( p, pRepr );
    p->nConeMax = AIG_MAX( p->nConeMax, p->nConeThis );
    // resimulate the cone of influence of the other nodes
    Vec_PtrForEachEntry( p->vRoots, pRoot, i )
        Dch_ManResimulateOther_rec( p, pRoot );
    // refine this class
    if ( Dch_ObjIsConst1Cand(p->pAigTotal, pObj) )
        RetValue = Dch_ClassesRefineConst1Group( p->ppClasses, p->vRoots, 0 );
    else
        RetValue = Dch_ClassesRefineOneClass( p->ppClasses, pRepr, 0 );
    assert( RetValue );
p->timeSimSat += clock() - clk;
}

/**Function*************************************************************

  Synopsis    [Performs fraiging for one node.]

  Description [Returns the fraiged node.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dch_ManSweepNode( Dch_Man_t * p, Aig_Obj_t * pObj )
{ 
    Aig_Obj_t * pObjRepr, * pObjFraig, * pObjFraig2, * pObjReprFraig;
    int RetValue;
    // get representative of this class
    pObjRepr = Aig_ObjRepr( p->pAigTotal, pObj );
    if ( pObjRepr == NULL )
        return;
    // get the fraiged node
    pObjFraig = Dch_ObjFraig( pObj );
    // get the fraiged representative
    pObjReprFraig = Dch_ObjFraig( pObjRepr );
    // if the fraiged nodes are the same, return
    if ( Aig_Regular(pObjFraig) == Aig_Regular(pObjReprFraig) )
    {
        // remember the proved equivalence
        p->pReprsProved[ pObj->Id ] = pObjRepr;
        return;
    }
    assert( Aig_Regular(pObjFraig) != Aig_ManConst1(p->pAigFraig) );
    RetValue = Dch_NodesAreEquiv( p, Aig_Regular(pObjReprFraig), Aig_Regular(pObjFraig) );
    if ( RetValue == -1 ) // timed out
        return;
    if ( RetValue == 1 )  // proved equivalent
    {
        pObjFraig2 = Aig_NotCond( pObjReprFraig, pObj->fPhase ^ pObjRepr->fPhase );
        Dch_ObjSetFraig( pObj, pObjFraig2 );
        // remember the proved equivalence
        p->pReprsProved[ pObj->Id ] = pObjRepr;
        return;
    }
    // disproved the equivalence
    Dch_ManSweepResimulate( p, pObj, pObjRepr );
}

/**Function*************************************************************

  Synopsis    [Performs fraiging for the internal nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Dch_ManSweep( Dch_Man_t * p )
{
    Bar_Progress_t * pProgress = NULL;
    Aig_Obj_t * pObj, * pObjNew;
    int i;
    // map constants and PIs
    p->pAigFraig = Aig_ManStart( Aig_ManObjNumMax(p->pAigTotal) );
    Aig_ManCleanData( p->pAigTotal );
    Aig_ManConst1(p->pAigTotal)->pData = Aig_ManConst1(p->pAigFraig);
    Aig_ManForEachPi( p->pAigTotal, pObj, i )
        pObj->pData = Aig_ObjCreatePi( p->pAigFraig );
    // prepare class refinement procedures
    Dch_ClassesSetData( p->ppClasses, NULL, NULL, Dch_NodeIsConstCex, Dch_NodesAreEqualCex );
    // sweep internal nodes
    pProgress = Bar_ProgressStart( stdout, Aig_ManObjNumMax(p->pAigTotal) );
    Aig_ManForEachNode( p->pAigTotal, pObj, i )
    {
        Bar_ProgressUpdate( pProgress, i, NULL );
        pObjNew = Aig_And( p->pAigFraig, Dch_ObjChild0Fra(pObj), Dch_ObjChild1Fra(pObj) );
        if ( pObjNew == NULL )
            continue;
        Dch_ObjSetFraig( pObj, pObjNew );
        Dch_ManSweepNode( p, pObj );
    }
    // update the representatives of the nodes (makes classes invalid)
    FREE( p->pAigTotal->pReprs );
    p->pAigTotal->pReprs = p->pReprsProved;
    p->pReprsProved = NULL;
    // clean the mark
    Aig_ManCleanMarkB( p->pAigTotal );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


