/**CFile****************************************************************

  FileName    [fraAnd.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Fraig FRAIG package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 30, 2007.]

  Revision    [$Id: fraAnd.c,v 1.00 2007/06/30 00:00:00 alanmi Exp $]

***********************************************************************/

#include "fra.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////


/**Function*************************************************************

  Synopsis    [Performs fraiging for one node.]

  Description [Returns the fraiged node.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Fra_And( Fra_Man_t * p, Aig_Obj_t * pObjOld )
{ 
    Aig_Obj_t * pObjOldRepr, * pObjFraig, * pFanin0Fraig, * pFanin1Fraig, * pObjOldReprFraig;
    int RetValue;
    assert( !Aig_IsComplement(pObjOld) );
    assert( Aig_ObjIsNode(pObjOld) );
    // get the fraiged fanins
    pFanin0Fraig = Fra_ObjChild0Fra(pObjOld);
    pFanin1Fraig = Fra_ObjChild1Fra(pObjOld);
    // get the fraiged node
    pObjFraig = Aig_And( p->pManFraig, pFanin0Fraig, pFanin1Fraig );
    if ( Aig_ObjIsConst1(Aig_Regular(pObjFraig)) )
        return pObjFraig;
    Aig_Regular(pObjFraig)->pData = p;
    // get representative of this class
    pObjOldRepr = Fra_ObjRepr(pObjOld);
    if ( pObjOldRepr == NULL || // this is a unique node
       (!p->pPars->fDoSparse && pObjOldRepr == Aig_ManConst1(p->pManAig)) ) // this is a sparse node
    {
        assert( Aig_Regular(pFanin0Fraig) != Aig_Regular(pFanin1Fraig) );
        assert( Aig_Regular(pObjFraig) != Aig_Regular(pFanin0Fraig) );
        assert( Aig_Regular(pObjFraig) != Aig_Regular(pFanin1Fraig) );
        return pObjFraig;
    }
    // get the fraiged representative
    pObjOldReprFraig = Fra_ObjFraig(pObjOldRepr);
    // if the fraiged nodes are the same, return
    if ( Aig_Regular(pObjFraig) == Aig_Regular(pObjOldReprFraig) )
        return pObjFraig;
    assert( Aig_Regular(pObjFraig) != Aig_ManConst1(p->pManFraig) );
//    printf( "Node = %d. Repr = %d.\n", pObjOld->Id, pObjOldRepr->Id );

    // if they are proved different, the c-ex will be in p->pPatWords
    RetValue = Fra_NodesAreEquiv( p, Aig_Regular(pObjOldReprFraig), Aig_Regular(pObjFraig) );
    if ( RetValue == 1 )  // proved equivalent
    {
//        pObjOld->fMarkA = 1;
        return Aig_NotCond( pObjOldReprFraig, pObjOld->fPhase ^ pObjOldRepr->fPhase );
    }
    if ( RetValue == -1 ) // failed
    {
        Aig_Obj_t * ppNodes[2] = { Aig_Regular(pObjOldReprFraig), Aig_Regular(pObjFraig) };
        Vec_Ptr_t * vNodes;

        if ( !p->pPars->fSpeculate )
            return pObjFraig;
        // substitute the node
//        pObjOld->fMarkB = 1;
        p->nSpeculs++;

        vNodes = Aig_ManDfsNodes( p->pManFraig, ppNodes, 2 );
        printf( "%d ", Vec_PtrSize(vNodes) );
        Vec_PtrFree( vNodes );

        return Aig_NotCond( pObjOldReprFraig, pObjOld->fPhase ^ pObjOldRepr->fPhase );
    }
//    printf( "Disproved %d and %d.\n", pObjOldRepr->Id, pObjOld->Id );
    // simulate the counter-example and return the Fraig node
//    printf( "Representaive before = %d.\n", Fra_ObjRepr(pObjOld)? Fra_ObjRepr(pObjOld)->Id : -1 );
    Fra_Resimulate( p );
//    printf( "Representaive after  = %d.\n", Fra_ObjRepr(pObjOld)? Fra_ObjRepr(pObjOld)->Id : -1 );
    assert( Fra_ObjRepr(pObjOld) != pObjOldRepr );
    return pObjFraig;
}

/**Function*************************************************************

  Synopsis    [Performs fraiging for the internal nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_Sweep( Fra_Man_t * p )
{
    Aig_Obj_t * pObj, * pObjNew;
    int i, k = 0;
p->nClassesZero = Vec_PtrSize(p->vClasses1);
p->nClassesBeg  = Vec_PtrSize(p->vClasses) + (int)(Vec_PtrSize(p->vClasses1) > 0);
    // duplicate internal nodes
//    p->pProgress = Extra_ProgressBarStart( stdout, Aig_ManNodeNum(p->pManAig) );
    Aig_ManForEachNode( p->pManAig, pObj, i )
    {
//        Extra_ProgressBarUpdate( p->pProgress, k++, NULL );
        // default to simple strashing if simulation detected a counter-example for a PO
        if ( p->pManFraig->pData )
            pObjNew = Aig_And( p->pManFraig, Fra_ObjChild0Fra(pObj), Fra_ObjChild1Fra(pObj) );
        else
            pObjNew = Fra_And( p, pObj ); // pObjNew can be complemented
        Fra_ObjSetFraig( pObj, pObjNew );
        assert( Fra_ObjFraig(pObj) != NULL );
    }
//    Extra_ProgressBarStop( p->pProgress );
p->nClassesEnd = Vec_PtrSize(p->vClasses) + (int)(Vec_PtrSize(p->vClasses1) > 0);
    // try to prove the outputs of the miter
    p->nNodesMiter = Aig_ManNodeNum(p->pManFraig);
//    Fra_MiterStatus( p->pManFraig );
//    if ( p->pPars->fProve && p->pManFraig->pData == NULL )
//        Fra_MiterProve( p );
    // add the POs
    Aig_ManForEachPo( p->pManAig, pObj, i )
        Aig_ObjCreatePo( p->pManFraig, Fra_ObjChild0Fra(pObj) );
    // remove dangling nodes 
    Aig_ManCleanup( p->pManFraig );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


