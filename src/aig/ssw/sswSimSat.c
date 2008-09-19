/**CFile****************************************************************

  FileName    [sswSimSat.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Inductive prover with constraints.]

  Synopsis    [Performs resimulation using counter-examples.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - September 1, 2008.]

  Revision    [$Id: sswSimSat.c,v 1.00 2008/09/01 00:00:00 alanmi Exp $]

***********************************************************************/

#include "sswInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Collects internal nodes in the reverse DFS order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ManCollectTfoCands_rec( Ssw_Man_t * p, Aig_Obj_t * pObj )
{
    Aig_Obj_t * pFanout, * pRepr;
    int iFanout = -1, i;
    assert( !Aig_IsComplement(pObj) );
    if ( Aig_ObjIsTravIdCurrent(p->pAig, pObj) )
        return;
    Aig_ObjSetTravIdCurrent(p->pAig, pObj);
    // traverse the fanouts
    Aig_ObjForEachFanout( p->pAig, pObj, pFanout, iFanout, i )
        Ssw_ManCollectTfoCands_rec( p, pFanout );
    // check if the given node has a representative
    pRepr = Aig_ObjRepr( p->pAig, pObj );
    if ( pRepr == NULL )
        return;
    // pRepr is the constant 1 node
    if ( pRepr == Aig_ManConst1(p->pAig) )
    {
        Vec_PtrPush( p->vSimRoots, pObj );
        return;
    }
    // pRepr is the representative of the equivalence class
    if ( Aig_ObjIsTravIdCurrent(p->pAig, pRepr) )
        return;
    Aig_ObjSetTravIdCurrent(p->pAig, pRepr);
    Vec_PtrPush( p->vSimClasses, pRepr );
}

/**Function*************************************************************

  Synopsis    [Collect equivalence classes and const1 cands in the TFO.]

  Description []
               
  SideEffects []

  SeeAlso     []
 
***********************************************************************/
void Ssw_ManCollectTfoCands( Ssw_Man_t * p, Aig_Obj_t * pObj1, Aig_Obj_t * pObj2 )
{
    Vec_PtrClear( p->vSimRoots );
    Vec_PtrClear( p->vSimClasses );
    Aig_ManIncrementTravId( p->pAig );
    Aig_ObjSetTravIdCurrent( p->pAig, Aig_ManConst1(p->pAig) );    
    Ssw_ManCollectTfoCands_rec( p, pObj1 );
    Ssw_ManCollectTfoCands_rec( p, pObj2 );
    Vec_PtrSort( p->vSimRoots,   Aig_ObjCompareIdIncrease );
    Vec_PtrSort( p->vSimClasses, Aig_ObjCompareIdIncrease );
}

/**Function*************************************************************

  Synopsis    [Retrives value of the PI in the original AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ssw_ManOriginalPiValue( Ssw_Man_t * p, Aig_Obj_t * pObj, int f )
{
    Aig_Obj_t * pObjFraig;
    int nVarNum, Value;
    assert( Aig_ObjIsPi(pObj) );
    pObjFraig = Ssw_ObjFraig( p, pObj, f );
    nVarNum = Ssw_ObjSatNum( p, Aig_Regular(pObjFraig) );
    Value = (!nVarNum)? 0 : (Aig_IsComplement(pObjFraig) ^ sat_solver_var_value( p->pSat, nVarNum ));
    if ( p->pPars->fPolarFlip )
    {
        if ( Aig_Regular(pObjFraig)->fPhase )  Value ^= 1;
    }
/*
    if ( nVarNum==0 )
        printf( "x" );
    else if ( Value == 0 )
        printf( "0" );
    else
        printf( "1" );
*/
    return Value;
}

/**Function*************************************************************

  Synopsis    [Resimulates the cone of influence of the solved nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []
 
***********************************************************************/
void Ssw_ManResimulateSolved_rec( Ssw_Man_t * p, Aig_Obj_t * pObj, int f )
{
    if ( Aig_ObjIsTravIdCurrent(p->pAig, pObj) )
        return;
    Aig_ObjSetTravIdCurrent(p->pAig, pObj);
    if ( Aig_ObjIsPi(pObj) )
    {
        pObj->fMarkB = Ssw_ManOriginalPiValue( p, pObj, f );
        return;
    }
    Ssw_ManResimulateSolved_rec( p, Aig_ObjFanin0(pObj), f );
    Ssw_ManResimulateSolved_rec( p, Aig_ObjFanin1(pObj), f );
    pObj->fMarkB = ( Aig_ObjFanin0(pObj)->fMarkB ^ Aig_ObjFaninC0(pObj) )
                 & ( Aig_ObjFanin1(pObj)->fMarkB ^ Aig_ObjFaninC1(pObj) );
}

/**Function*************************************************************

  Synopsis    [Resimulates the cone of influence of the other nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ManResimulateOther_rec( Ssw_Man_t * p, Aig_Obj_t * pObj )
{
    if ( Aig_ObjIsTravIdCurrent(p->pAig, pObj) )
        return;
    Aig_ObjSetTravIdCurrent(p->pAig, pObj);
    if ( Aig_ObjIsPi(pObj) )
    {
        // set random value
        pObj->fMarkB = Aig_ManRandom(0) & 1;
        return;
    }
    Ssw_ManResimulateOther_rec( p, Aig_ObjFanin0(pObj) );
    Ssw_ManResimulateOther_rec( p, Aig_ObjFanin1(pObj) );
    pObj->fMarkB = ( Aig_ObjFanin0(pObj)->fMarkB ^ Aig_ObjFaninC0(pObj) )
                 & ( Aig_ObjFanin1(pObj)->fMarkB ^ Aig_ObjFaninC1(pObj) );
}

/**Function*************************************************************

  Synopsis    [Handle the counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ManResimulateCex( Ssw_Man_t * p, Aig_Obj_t * pObj, Aig_Obj_t * pRepr, int f )
{
    Aig_Obj_t * pRoot, ** ppClass;
    int i, k, nSize, RetValue1, RetValue2, clk = clock();
    // get the equivalence classes
    Ssw_ManCollectTfoCands( p, pObj, pRepr );
    // resimulate the cone of influence of the solved nodes
    Aig_ManIncrementTravId( p->pAig );
    Aig_ObjSetTravIdCurrent( p->pAig, Aig_ManConst1(p->pAig) );
    Ssw_ManResimulateSolved_rec( p, pObj, f );
    Ssw_ManResimulateSolved_rec( p, pRepr, f );
    // resimulate the cone of influence of the other nodes
    Vec_PtrForEachEntry( p->vSimRoots, pRoot, i )
        Ssw_ManResimulateOther_rec( p, pRoot );
    // refine these nodes
    RetValue1 = Ssw_ClassesRefineConst1Group( p->ppClasses, p->vSimRoots, 0 );
    // resimulate the cone of influence of the cand classes
    RetValue2 = 0;
    Vec_PtrForEachEntry( p->vSimClasses, pRoot, i )
    {
        ppClass = Ssw_ClassesReadClass( p->ppClasses, pRoot, &nSize );
        for ( k = 0; k < nSize; k++ )
            Ssw_ManResimulateOther_rec( p, ppClass[k] );
        // refine this class
        RetValue2 += Ssw_ClassesRefineOneClass( p->ppClasses, pRoot, 0 );
    }
    // make sure refinement happened
    if ( Aig_ObjIsConst1(pRepr) )
        assert( RetValue1 );
    else
        assert( RetValue2 );
p->timeSimSat += clock() - clk;
}

/**Function*************************************************************

  Synopsis    [Handle the counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ManResimulateCexTotal( Ssw_Man_t * p, Aig_Obj_t * pCand, Aig_Obj_t * pRepr, int f )
{
    Aig_Obj_t * pObj;
    int i, RetValue1, RetValue2, clk = clock();
    // set the PI simulation information
    Aig_ManConst1(p->pAig)->fMarkB = 1;
    Aig_ManForEachPi( p->pAig, pObj, i )
        pObj->fMarkB = Aig_InfoHasBit( p->pPatWords, i );
    // simulate internal nodes
    Aig_ManForEachNode( p->pAig, pObj, i )
        pObj->fMarkB = ( Aig_ObjFanin0(pObj)->fMarkB ^ Aig_ObjFaninC0(pObj) )
                     & ( Aig_ObjFanin1(pObj)->fMarkB ^ Aig_ObjFaninC1(pObj) );
    // check equivalence classes
    RetValue1 = Ssw_ClassesRefineConst1( p->ppClasses, 0 );
    RetValue2 = Ssw_ClassesRefine( p->ppClasses, 0 );
    // make sure refinement happened
    if ( Aig_ObjIsConst1(pRepr) ) 
    {
        assert( RetValue1 );
        if ( RetValue1 == 0 )
            printf( "\nSsw_ManResimulateCexTotal() Error: RetValue1 does not hold.\n" );
    }
    else
    {
        assert( RetValue2 );
        if ( RetValue2 == 0 )
            printf( "\nSsw_ManResimulateCexTotal() Error: RetValue2 does not hold.\n" );
    }
p->timeSimSat += clock() - clk;
}


/**Function*************************************************************

  Synopsis    [Handle the counter-example.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ssw_ManResimulateCexTotalSim( Ssw_Man_t * p, Aig_Obj_t * pCand, Aig_Obj_t * pRepr, int f )
{
    int RetValue1, RetValue2, clk = clock();
    // set the PI simulation information
    Ssw_SmlAssignDist1Plus( p->pSml, p->pPatWords );
    // simulate internal nodes
    Ssw_SmlSimulateOne( p->pSml );
    // check equivalence classes
    RetValue1 = Ssw_ClassesRefineConst1( p->ppClasses, 1 );
    RetValue2 = Ssw_ClassesRefine( p->ppClasses, 1 );
    // make sure refinement happened
    if ( Aig_ObjIsConst1(pRepr) )
    {
        assert( RetValue1 );
        if ( RetValue1 == 0 )
            printf( "\nSsw_ManResimulateCexTotalSim() Error: RetValue1 does not hold.\n" );
    }
    else
    {
        assert( RetValue2 );
        if ( RetValue2 == 0 )
            printf( "\nSsw_ManResimulateCexTotalSim() Error: RetValue2 does not hold.\n" );
    }
p->timeSimSat += clock() - clk;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


