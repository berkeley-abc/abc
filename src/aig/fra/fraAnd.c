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
Dar_Obj_t * Fra_And( Fra_Man_t * p, Dar_Obj_t * pObjOld )
{ 
    Dar_Obj_t * pObjOldRepr, * pObjFraig, * pFanin0Fraig, * pFanin1Fraig, * pObjOldReprFraig;
    int RetValue;
    assert( !Dar_IsComplement(pObjOld) );
    assert( Dar_ObjIsNode(pObjOld) );
    // get the fraiged fanins
    pFanin0Fraig = Fra_ObjChild0Fra(pObjOld);
    pFanin1Fraig = Fra_ObjChild1Fra(pObjOld);
    // get the fraiged node
    pObjFraig = Dar_And( p->pManFraig, pFanin0Fraig, pFanin1Fraig );
    Dar_Regular(pObjFraig)->pData = p;
    // get representative of this class
    pObjOldRepr = Fra_ObjRepr(pObjOld);
    if ( pObjOldRepr == NULL || // this is a unique node
       (!p->pPars->fDoSparse && pObjOldRepr == Dar_ManConst1(p->pManAig)) ) // this is a sparse node
    {
        assert( Dar_Regular(pFanin0Fraig) != Dar_Regular(pFanin1Fraig) );
        assert( Dar_Regular(pObjFraig) != Dar_Regular(pFanin0Fraig) );
        assert( Dar_Regular(pObjFraig) != Dar_Regular(pFanin1Fraig) );
        return pObjFraig;
    }
    // get the fraiged representative
    pObjOldReprFraig = Fra_ObjFraig(pObjOldRepr);
    // if the fraiged nodes are the same, return
    if ( Dar_Regular(pObjFraig) == Dar_Regular(pObjOldReprFraig) )
        return pObjFraig;
    assert( Dar_Regular(pObjFraig) != Dar_ManConst1(p->pManFraig) );
//    printf( "Node = %d. Repr = %d.\n", pObjOld->Id, pObjOldRepr->Id );

    // if they are proved different, the c-ex will be in p->pPatWords
    RetValue = Fra_NodesAreEquiv( p, Dar_Regular(pObjOldReprFraig), Dar_Regular(pObjFraig) );
    if ( RetValue == 1 )  // proved equivalent
    {
//        pObjOld->fMarkA = 1;
        return Dar_NotCond( pObjOldReprFraig, pObjOld->fPhase ^ pObjOldRepr->fPhase );
    }
    if ( RetValue == -1 ) // failed
    {
        if ( !p->pPars->fSpeculate )
            return pObjFraig;
        // substitute the node
//        pObjOld->fMarkB = 1;
        return Dar_NotCond( pObjOldReprFraig, pObjOld->fPhase ^ pObjOldRepr->fPhase );
    }
    // simulate the counter-example and return the Fraig node
    Fra_Resimulate( p );
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
    Dar_Obj_t * pObj, * pObjNew;
    int i, k = 0;
p->nClassesZero = Vec_PtrSize(p->vClasses1);
p->nClassesBeg  = Vec_PtrSize(p->vClasses) + (int)(Vec_PtrSize(p->vClasses1) > 0);
    // duplicate internal nodes
//    p->pProgress = Extra_ProgressBarStart( stdout, Dar_ManNodeNum(p->pManAig) );
    Dar_ManForEachNode( p->pManAig, pObj, i )
    {
//        Extra_ProgressBarUpdate( p->pProgress, k++, NULL );
        // default to simple strashing if simulation detected a counter-example for a PO
        if ( p->pManFraig->pData )
            pObjNew = Dar_And( p->pManFraig, Fra_ObjChild0Fra(pObj), Fra_ObjChild1Fra(pObj) );
        else
            pObjNew = Fra_And( p, pObj ); // pObjNew can be complemented
        Fra_ObjSetFraig( pObj, pObjNew );
        assert( Fra_ObjFraig(pObj) != NULL );
    }
//    Extra_ProgressBarStop( p->pProgress );
p->nClassesEnd = Vec_PtrSize(p->vClasses) + (int)(Vec_PtrSize(p->vClasses1) > 0);
    // try to prove the outputs of the miter
    p->nNodesMiter = Dar_ManNodeNum(p->pManFraig);
//    Fra_MiterStatus( p->pManFraig );
//    if ( p->pPars->fProve && p->pManFraig->pData == NULL )
//        Fra_MiterProve( p );
    // add the POs
    Dar_ManForEachPo( p->pManAig, pObj, i )
        Dar_ObjCreatePo( p->pManFraig, Fra_ObjChild0Fra(pObj) );
    // remove dangling nodes 
    Dar_ManCleanup( p->pManFraig );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


