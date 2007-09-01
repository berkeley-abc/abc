/**CFile****************************************************************

  FileName    [lpkAbcDec.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Fast Boolean matching for LUT structures.]

  Synopsis    [The new core procedure.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: lpkAbcDec.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "lpkInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Implements the function.]

  Description [Returns the node implementing this function.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Lpk_ImplementFun( Abc_Ntk_t * pNtk, Vec_Ptr_t * vLeaves, Lpk_Fun_t * p )
{
    Abc_Obj_t * pObjNew;
    int i;
    pObjNew = Abc_NtkCreateNode( pNtk );
    for ( i = 0; i < (int)p->nVars; i++ )
        Abc_ObjAddFanin( pObjNew, Vec_PtrEntry(vLeaves, p->pFanins[i]) );
    Abc_ObjLevelNew( pObjNew );
    // create the logic function
    {
        extern Hop_Obj_t * Kit_GraphToHop( Hop_Man_t * pMan, Kit_Graph_t * pGraph );
        // allocate memory for the ISOP
        Vec_Int_t * vCover = Vec_IntAlloc( 0 );
        // transform truth table into the decomposition tree
        Kit_Graph_t * pGraph = Kit_TruthToGraph( Lpk_FunTruth(p, 0), p->nVars, vCover );
        // derive the AIG for the decomposition tree
        pObjNew->pData = Kit_GraphToHop( pNtk->pManFunc, pGraph );
        Kit_GraphFree( pGraph );
        Vec_IntFree( vCover );
    }
    return pObjNew;
}

/**Function*************************************************************

  Synopsis    [Implements the function.]

  Description [Returns the node implementing this function.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Lpk_Implement( Abc_Ntk_t * pNtk, Vec_Ptr_t * vLeaves, int nLeavesOld )
{
    Lpk_Fun_t * pFun;
    Abc_Obj_t * pRes;
    int i;
    for ( i = Vec_PtrSize(vLeaves) - 1; i >= nLeavesOld; i-- )
    {
        pFun = Vec_PtrEntry( vLeaves, i );
        pRes = Lpk_ImplementFun( pNtk, vLeaves, pFun );
        Vec_PtrWriteEntry( vLeaves, i, pRes );
        Lpk_FunFree( pFun );
    }
    return pRes;
}

/**Function*************************************************************

  Synopsis    [Decomposes the function using recursive MUX decomposition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Lpk_Decompose_rec( Lpk_Fun_t * p )
{
    Lpk_Fun_t * p2;
    int VarPol;
    assert( p->nAreaLim > 0 );
    if ( p->nVars <= p->nLutK )
        return 1;
    // check if decomposition exists
    VarPol = Lpk_MuxAnalize( p );
    if ( VarPol == -1 )
        return 0;
    // split and call recursively
    p2 = Lpk_MuxSplit( p, VarPol );
    if ( !Lpk_Decompose_rec( p2 ) )
        return 0;
    return Lpk_Decompose_rec( p );
}


/**Function*************************************************************

  Synopsis    [Decomposes the function using recursive MUX decomposition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Lpk_Decompose( Abc_Ntk_t * pNtk, Vec_Ptr_t * vLeaves, unsigned * pTruth, int nLutK, int AreaLim, int DelayLim )
{
    Lpk_Fun_t * p;
    Abc_Obj_t * pObjNew = NULL;
    int i, nLeaves;
    // create the starting function
    nLeaves = Vec_PtrSize( vLeaves );
    p = Lpk_FunCreate( pNtk, vLeaves, pTruth, nLutK, AreaLim, DelayLim );
    Lpk_FunSuppMinimize( p );
    // decompose the function 
    if ( Lpk_Decompose_rec(p) )
        pObjNew = Lpk_Implement( pNtk, vLeaves, nLeaves );
    else
    {
        for ( i = Vec_PtrSize(vLeaves) - 1; i >= nLeaves; i-- )
            Lpk_FunFree( Vec_PtrEntry(vLeaves, i) );
    }
    Vec_PtrShrink( vLeaves, nLeaves );
    return pObjNew;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


