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
    extern Hop_Obj_t * Kit_TruthToHop( Hop_Man_t * pMan, unsigned * pTruth, int nVars, Vec_Int_t * vMemory );
    unsigned * pTruth;
    Abc_Obj_t * pObjNew;
    int i;
    // create the new node
    pObjNew = Abc_NtkCreateNode( pNtk );
    for ( i = 0; i < (int)p->nVars; i++ )
        Abc_ObjAddFanin( pObjNew, Vec_PtrEntry(vLeaves, p->pFanins[i]) );
    Abc_ObjLevelNew( pObjNew );
    // assign the node's function
    pTruth = Lpk_FunTruth(p, 0);
    if ( p->nVars == 0 )
    {
        pObjNew->pData = Hop_NotCond( Hop_ManConst1(pNtk->pManFunc), !(pTruth[0] & 1) );
        return pObjNew;
    }
    if ( p->nVars == 1 )
    {
        pObjNew->pData = Hop_NotCond( Hop_ManPi(pNtk->pManFunc, 0), (pTruth[0] & 1) );
        return pObjNew;
    }
    // create the logic function
    pObjNew->pData = Kit_TruthToHop( pNtk->pManFunc, pTruth, p->nVars, NULL );
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
    Vec_PtrShrink( vLeaves, nLeavesOld );
    return pRes;
}

/**Function*************************************************************

  Synopsis    [Decomposes the function using recursive MUX decomposition.]

  Description [Returns the ID of the top-most decomposition node 
  implementing this function, or 0 if there is no decomposition satisfying
  the constraints on area and delay.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Lpk_Decompose_rec( Lpk_Fun_t * p )
{
    Lpk_Res_t * pResMux, * pResDsd;
    Lpk_Fun_t * p2;
    // is only called for non-trivial blocks
    assert( p->nLutK >= 3 && p->nLutK <= 6 );
    assert( p->nVars > p->nLutK );
    // skip if area bound is exceeded
    if ( Lpk_LutNumLuts(p->nVars, p->nLutK) > (int)p->nAreaLim )
        return 0;
    // skip if delay bound is exceeded
    if ( Lpk_SuppDelay(p->uSupp, p->pDelays) > (int)p->nDelayLim )
        return 0;
    // check MUX decomposition
    pResMux = Lpk_MuxAnalize( p );
    assert( !pResMux || (pResMux->DelayEst <= (int)p->nDelayLim && pResMux->AreaEst <= (int)p->nAreaLim) );
    // accept MUX decomposition if it is "good"
    if ( pResMux && pResMux->nSuppSizeS <= (int)p->nLutK && pResMux->nSuppSizeL <= (int)p->nLutK )
        pResDsd = NULL;
    else
    {
        pResDsd = Lpk_DsdAnalize( p );
        assert( !pResDsd || (pResDsd->DelayEst <= (int)p->nDelayLim && pResDsd->AreaEst <= (int)p->nAreaLim) );
    }
    if ( pResMux && pResDsd )
    {
        // compare two decompositions
        if ( pResMux->AreaEst < pResDsd->AreaEst || 
            (pResMux->AreaEst == pResDsd->AreaEst && pResMux->nSuppSizeL < pResDsd->nSuppSizeL) || 
            (pResMux->AreaEst == pResDsd->AreaEst && pResMux->nSuppSizeL == pResDsd->nSuppSizeL && pResMux->DelayEst < pResDsd->DelayEst) )
            pResDsd = NULL;
        else
            pResMux = NULL;
    }
    assert( pResMux == NULL || pResDsd == NULL );
    if ( pResMux )
    {
        p2 = Lpk_MuxSplit( p, pResMux->pCofVars[0], pResMux->Polarity );
        if ( p2->nVars > p->nLutK && !Lpk_Decompose_rec( p2 ) )
            return 0;
        if ( p->nVars > p->nLutK && !Lpk_Decompose_rec( p ) )
            return 0;
        return 1;
    }
    if ( pResDsd )
    {
        p2 = Lpk_DsdSplit( p, pResDsd->pCofVars, pResDsd->nCofVars, pResDsd->BSVars );
        assert( p2->nVars <= (int)p->nLutK );
        if ( p->nVars > p->nLutK && !Lpk_Decompose_rec( p ) )
            return 0;
        return 1;
    }
    return 0;
}

/**Function*************************************************************

  Synopsis    [Removes decomposed nodes from the array of fanins.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Lpk_DecomposeClean( Vec_Ptr_t * vLeaves, int nLeavesOld )
{
    Lpk_Fun_t * pFunc;
    int i;
    Vec_PtrForEachEntryStart( vLeaves, pFunc, i, nLeavesOld )
        Lpk_FunFree( pFunc );
    Vec_PtrShrink( vLeaves, nLeavesOld );
}

/**Function*************************************************************

  Synopsis    [Decomposes the function using recursive MUX decomposition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Lpk_Decompose( Abc_Ntk_t * pNtk, Vec_Ptr_t * vLeaves, unsigned * pTruth, int nLutK, int AreaLim, int DelayLim )
{
    Lpk_Fun_t * pFun;
    Abc_Obj_t * pObjNew = NULL;
    int nLeaves = Vec_PtrSize( vLeaves );
    pFun = Lpk_FunCreate( pNtk, vLeaves, pTruth, nLutK, AreaLim, DelayLim );
    Lpk_FunSuppMinimize( pFun );
    if ( pFun->nVars <= pFun->nLutK )
        pObjNew = Lpk_ImplementFun( pNtk, vLeaves, pFun );
    else if ( Lpk_Decompose_rec(pFun) )
        pObjNew = Lpk_Implement( pNtk, vLeaves, nLeaves );
    Lpk_DecomposeClean( vLeaves, nLeaves );
    return pObjNew;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


