/**CFile****************************************************************

  FileName    [cecCnf.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinatinoal equivalence checking.]

  Synopsis    [CNF computation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecCnf.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "cecInt.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Addes clauses to the solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_AddClausesMux( Cec_ManSat_t * p, Aig_Obj_t * pNode )
{
    Aig_Obj_t * pNodeI, * pNodeT, * pNodeE;
    int pLits[4], RetValue, VarF, VarI, VarT, VarE, fCompT, fCompE;

    assert( !Aig_IsComplement( pNode ) );
    assert( Aig_ObjIsMuxType( pNode ) );
    // get nodes (I = if, T = then, E = else)
    pNodeI = Aig_ObjRecognizeMux( pNode, &pNodeT, &pNodeE );
    // get the variable numbers
    VarF = Cec_ObjSatNum(p,pNode);
    VarI = Cec_ObjSatNum(p,pNodeI);
    VarT = Cec_ObjSatNum(p,Aig_Regular(pNodeT));
    VarE = Cec_ObjSatNum(p,Aig_Regular(pNodeE));
    // get the complementation flags
    fCompT = Aig_IsComplement(pNodeT);
    fCompE = Aig_IsComplement(pNodeE);

    // f = ITE(i, t, e)

    // i' + t' + f
    // i' + t  + f'
    // i  + e' + f
    // i  + e  + f'

    // create four clauses
    pLits[0] = toLitCond(VarI, 1);
    pLits[1] = toLitCond(VarT, 1^fCompT);
    pLits[2] = toLitCond(VarF, 0);
    if ( p->pPars->fPolarFlip )
    {
        if ( pNodeI->fPhase )               pLits[0] = lit_neg( pLits[0] );
        if ( Aig_Regular(pNodeT)->fPhase )  pLits[1] = lit_neg( pLits[1] );
        if ( pNode->fPhase )                pLits[2] = lit_neg( pLits[2] );
    }
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );
    pLits[0] = toLitCond(VarI, 1);
    pLits[1] = toLitCond(VarT, 0^fCompT);
    pLits[2] = toLitCond(VarF, 1);
    if ( p->pPars->fPolarFlip )
    {
        if ( pNodeI->fPhase )               pLits[0] = lit_neg( pLits[0] );
        if ( Aig_Regular(pNodeT)->fPhase )  pLits[1] = lit_neg( pLits[1] );
        if ( pNode->fPhase )                pLits[2] = lit_neg( pLits[2] );
    }
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );
    pLits[0] = toLitCond(VarI, 0);
    pLits[1] = toLitCond(VarE, 1^fCompE);
    pLits[2] = toLitCond(VarF, 0);
    if ( p->pPars->fPolarFlip )
    {
        if ( pNodeI->fPhase )               pLits[0] = lit_neg( pLits[0] );
        if ( Aig_Regular(pNodeE)->fPhase )  pLits[1] = lit_neg( pLits[1] );
        if ( pNode->fPhase )                pLits[2] = lit_neg( pLits[2] );
    }
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );
    pLits[0] = toLitCond(VarI, 0);
    pLits[1] = toLitCond(VarE, 0^fCompE);
    pLits[2] = toLitCond(VarF, 1);
    if ( p->pPars->fPolarFlip )
    {
        if ( pNodeI->fPhase )               pLits[0] = lit_neg( pLits[0] );
        if ( Aig_Regular(pNodeE)->fPhase )  pLits[1] = lit_neg( pLits[1] );
        if ( pNode->fPhase )                pLits[2] = lit_neg( pLits[2] );
    }
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );

    // two additional clauses
    // t' & e' -> f'
    // t  & e  -> f 

    // t  + e   + f'
    // t' + e'  + f 

    if ( VarT == VarE )
    {
//        assert( fCompT == !fCompE );
        return;
    }

    pLits[0] = toLitCond(VarT, 0^fCompT);
    pLits[1] = toLitCond(VarE, 0^fCompE);
    pLits[2] = toLitCond(VarF, 1);
    if ( p->pPars->fPolarFlip )
    {
        if ( Aig_Regular(pNodeT)->fPhase )  pLits[0] = lit_neg( pLits[0] );
        if ( Aig_Regular(pNodeE)->fPhase )  pLits[1] = lit_neg( pLits[1] );
        if ( pNode->fPhase )                pLits[2] = lit_neg( pLits[2] );
    }
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );
    pLits[0] = toLitCond(VarT, 1^fCompT);
    pLits[1] = toLitCond(VarE, 1^fCompE);
    pLits[2] = toLitCond(VarF, 0);
    if ( p->pPars->fPolarFlip )
    {
        if ( Aig_Regular(pNodeT)->fPhase )  pLits[0] = lit_neg( pLits[0] );
        if ( Aig_Regular(pNodeE)->fPhase )  pLits[1] = lit_neg( pLits[1] );
        if ( pNode->fPhase )                pLits[2] = lit_neg( pLits[2] );
    }
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 3 );
    assert( RetValue );
}

/**Function*************************************************************

  Synopsis    [Addes clauses to the solver.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_AddClausesSuper( Cec_ManSat_t * p, Aig_Obj_t * pNode, Vec_Ptr_t * vSuper )
{
    Aig_Obj_t * pFanin;
    int * pLits, nLits, RetValue, i;
    assert( !Aig_IsComplement(pNode) );
    assert( Aig_ObjIsNode( pNode ) );
    // create storage for literals
    nLits = Vec_PtrSize(vSuper) + 1;
    pLits = ALLOC( int, nLits );
    // suppose AND-gate is A & B = C
    // add !A => !C   or   A + !C
    Vec_PtrForEachEntry( vSuper, pFanin, i )
    {
        pLits[0] = toLitCond(Cec_ObjSatNum(p,Aig_Regular(pFanin)), Aig_IsComplement(pFanin));
        pLits[1] = toLitCond(Cec_ObjSatNum(p,pNode), 1);
        if ( p->pPars->fPolarFlip )
        {
            if ( Aig_Regular(pFanin)->fPhase )  pLits[0] = lit_neg( pLits[0] );
            if ( pNode->fPhase )                pLits[1] = lit_neg( pLits[1] );
        }
        RetValue = sat_solver_addclause( p->pSat, pLits, pLits + 2 );
        assert( RetValue );
    }
    // add A & B => C   or   !A + !B + C
    Vec_PtrForEachEntry( vSuper, pFanin, i )
    {
        pLits[i] = toLitCond(Cec_ObjSatNum(p,Aig_Regular(pFanin)), !Aig_IsComplement(pFanin));
        if ( p->pPars->fPolarFlip )
        {
            if ( Aig_Regular(pFanin)->fPhase )  pLits[i] = lit_neg( pLits[i] );
        }
    }
    pLits[nLits-1] = toLitCond(Cec_ObjSatNum(p,pNode), 0);
    if ( p->pPars->fPolarFlip )
    {
        if ( pNode->fPhase )  pLits[nLits-1] = lit_neg( pLits[nLits-1] );
    }
    RetValue = sat_solver_addclause( p->pSat, pLits, pLits + nLits );
    assert( RetValue );
    free( pLits );
}

/**Function*************************************************************

  Synopsis    [Collects the supergate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_CollectSuper_rec( Aig_Obj_t * pObj, Vec_Ptr_t * vSuper, int fFirst, int fUseMuxes )
{
    // if the new node is complemented or a PI, another gate begins
    if ( Aig_IsComplement(pObj) || Aig_ObjIsPi(pObj) || 
         (!fFirst && Aig_ObjRefs(pObj) > 1) || 
         (fUseMuxes && Aig_ObjIsMuxType(pObj)) )
    {
        Vec_PtrPushUnique( vSuper, pObj );
        return;
    }
    // go through the branches
    Cec_CollectSuper_rec( Aig_ObjChild0(pObj), vSuper, 0, fUseMuxes );
    Cec_CollectSuper_rec( Aig_ObjChild1(pObj), vSuper, 0, fUseMuxes );
}

/**Function*************************************************************

  Synopsis    [Collects the supergate.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_CollectSuper( Aig_Obj_t * pObj, int fUseMuxes, Vec_Ptr_t * vSuper )
{
    assert( !Aig_IsComplement(pObj) );
    assert( !Aig_ObjIsPi(pObj) );
    Vec_PtrClear( vSuper );
    Cec_CollectSuper_rec( pObj, vSuper, 1, fUseMuxes );
}

/**Function*************************************************************

  Synopsis    [Updates the solver clause database.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_ObjAddToFrontier( Cec_ManSat_t * p, Aig_Obj_t * pObj, Vec_Ptr_t * vFrontier )
{
    assert( !Aig_IsComplement(pObj) );
    if ( Cec_ObjSatNum(p,pObj) )
        return;
    assert( Cec_ObjSatNum(p,pObj) == 0 );
    if ( Aig_ObjIsConst1(pObj) )
        return;
    Vec_PtrPush( p->vUsedNodes, pObj );
    Cec_ObjSetSatNum( p, pObj, p->nSatVars++ );
    if ( Aig_ObjIsNode(pObj) )
        Vec_PtrPush( vFrontier, pObj );
}

/**Function*************************************************************

  Synopsis    [Updates the solver clause database.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Cec_CnfNodeAddToSolver( Cec_ManSat_t * p, Aig_Obj_t * pObj )
{ 
    Vec_Ptr_t * vFrontier;
    Aig_Obj_t * pNode, * pFanin;
    int i, k, fUseMuxes = 1;
    // quit if CNF is ready
    if ( Cec_ObjSatNum(p,pObj) )
        return;
    // start the frontier
    vFrontier = Vec_PtrAlloc( 100 );
    Cec_ObjAddToFrontier( p, pObj, vFrontier );
    // explore nodes in the frontier
    Vec_PtrForEachEntry( vFrontier, pNode, i )
    {
        // create the supergate
        assert( Cec_ObjSatNum(p,pNode) );
        if ( fUseMuxes && Aig_ObjIsMuxType(pNode) )
        {
            Vec_PtrClear( p->vFanins );
            Vec_PtrPushUnique( p->vFanins, Aig_ObjFanin0( Aig_ObjFanin0(pNode) ) );
            Vec_PtrPushUnique( p->vFanins, Aig_ObjFanin0( Aig_ObjFanin1(pNode) ) );
            Vec_PtrPushUnique( p->vFanins, Aig_ObjFanin1( Aig_ObjFanin0(pNode) ) );
            Vec_PtrPushUnique( p->vFanins, Aig_ObjFanin1( Aig_ObjFanin1(pNode) ) );
            Vec_PtrForEachEntry( p->vFanins, pFanin, k )
                Cec_ObjAddToFrontier( p, Aig_Regular(pFanin), vFrontier );
            Cec_AddClausesMux( p, pNode );
        }
        else
        {
            Cec_CollectSuper( pNode, fUseMuxes, p->vFanins );
            Vec_PtrForEachEntry( p->vFanins, pFanin, k )
                Cec_ObjAddToFrontier( p, Aig_Regular(pFanin), vFrontier );
            Cec_AddClausesSuper( p, pNode, p->vFanins );
        }
        assert( Vec_PtrSize(p->vFanins) > 1 );
    }
    Vec_PtrFree( vFrontier );
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


