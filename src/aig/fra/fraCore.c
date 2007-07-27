/**CFile****************************************************************

  FileName    [fraCore.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [New FRAIG package.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 30, 2007.]

  Revision    [$Id: fraCore.c,v 1.00 2007/06/30 00:00:00 alanmi Exp $]

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
Aig_Obj_t * Fra_And( Fra_Man_t * p, Aig_Obj_t * pObj )
{ 
    Aig_Obj_t * pObjRepr, * pObjFraig, * pFanin0Fraig, * pFanin1Fraig, * pObjReprFraig;
    int RetValue;
    assert( !Aig_IsComplement(pObj) );
    assert( Aig_ObjIsNode(pObj) );
    // get the fraiged fanins
    pFanin0Fraig = Fra_ObjChild0Fra(pObj,0);
    pFanin1Fraig = Fra_ObjChild1Fra(pObj,0);
    // get the fraiged node
    pObjFraig = Aig_And( p->pManFraig, pFanin0Fraig, pFanin1Fraig );
    if ( Aig_ObjIsConst1(Aig_Regular(pObjFraig)) )
        return pObjFraig;
    Aig_Regular(pObjFraig)->pData = p;
    // get representative of this class
    pObjRepr = Fra_ClassObjRepr(pObj);
    if ( pObjRepr == NULL || // this is a unique node
       (!p->pPars->fDoSparse && pObjRepr == Aig_ManConst1(p->pManAig)) ) // this is a sparse node
    {
        assert( Aig_Regular(pFanin0Fraig) != Aig_Regular(pFanin1Fraig) );
        assert( Aig_Regular(pObjFraig) != Aig_Regular(pFanin0Fraig) );
        assert( Aig_Regular(pObjFraig) != Aig_Regular(pFanin1Fraig) );
        return pObjFraig;
    }
    // get the fraiged representative
    pObjReprFraig = Fra_ObjFraig(pObjRepr,0);
    // if the fraiged nodes are the same, return
    if ( Aig_Regular(pObjFraig) == Aig_Regular(pObjReprFraig) )
        return pObjFraig;
    assert( Aig_Regular(pObjFraig) != Aig_ManConst1(p->pManFraig) );
//    printf( "Node = %d. Repr = %d.\n", pObj->Id, pObjRepr->Id );

    // if they are proved different, the c-ex will be in p->pPatWords
    RetValue = Fra_NodesAreEquiv( p, Aig_Regular(pObjReprFraig), Aig_Regular(pObjFraig) );
    if ( RetValue == 1 )  // proved equivalent
    {
//        pObj->fMarkA = 1;
//        if ( p->pPars->fChoicing )
//            Aig_ObjCreateRepr( p->pManFraig, Aig_Regular(pObjReprFraig), Aig_Regular(pObjFraig) );
        return Aig_NotCond( pObjReprFraig, pObj->fPhase ^ pObjRepr->fPhase );
    }
    if ( RetValue == -1 ) // failed
    {
        static int Counter = 0;
        char FileName[20];
        Aig_Man_t * pTemp;
        Aig_Obj_t * pNode;
        int i;

        Aig_Obj_t * ppNodes[2] = { Aig_Regular(pObjReprFraig), Aig_Regular(pObjFraig) };
//        Vec_Ptr_t * vNodes;

        Vec_PtrPush( p->vTimeouts, pObj );
        if ( !p->pPars->fSpeculate )
            return pObjFraig;
        // substitute the node
//        pObj->fMarkB = 1;
        p->nSpeculs++;

        pTemp = Aig_ManExtractMiter( p->pManFraig, ppNodes, 2 );
        sprintf( FileName, "aig\\%03d.blif", ++Counter );
        Aig_ManDumpBlif( pTemp, FileName );
        printf( "Speculation cone with %d nodes was written into file \"%s\".\n", Aig_ManNodeNum(pTemp), FileName );
        Aig_ManStop( pTemp );

        Aig_ManForEachObj( p->pManFraig, pNode, i )
            pNode->pData = p;

//        vNodes = Aig_ManDfsNodes( p->pManFraig, ppNodes, 2 );
//        printf( "Cone=%d ", Vec_PtrSize(vNodes) );
//        Vec_PtrFree( vNodes );

        return Aig_NotCond( pObjReprFraig, pObj->fPhase ^ pObjRepr->fPhase );
    }
    // simulate the counter-example and return the Fraig node
    Fra_Resimulate( p );
    assert( Fra_ClassObjRepr(pObj) != pObjRepr );
    return pObjFraig;
}

/**Function*************************************************************

  Synopsis    [Performs fraiging for the internal nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Fra_FraigSweep( Fra_Man_t * p )
{
    ProgressBar * pProgress;
    Aig_Obj_t * pObj, * pObjNew;
    int i, k = 0;
p->nClassesZero = Vec_PtrSize(p->pCla->vClasses1);
p->nClassesBeg  = Vec_PtrSize(p->pCla->vClasses) + (int)(Vec_PtrSize(p->pCla->vClasses1) > 0);
    // duplicate internal nodes
    pProgress = Extra_ProgressBarStart( stdout, Aig_ManObjIdMax(p->pManAig) );
    Aig_ManForEachNode( p->pManAig, pObj, i )
    {
        Extra_ProgressBarUpdate( pProgress, i, NULL );
        // default to simple strashing if simulation detected a counter-example for a PO
        if ( p->pManFraig->pData )
            pObjNew = Aig_And( p->pManFraig, Fra_ObjChild0Fra(pObj,0), Fra_ObjChild1Fra(pObj,0) );
        else
            pObjNew = Fra_And( p, pObj ); // pObjNew can be complemented
        Fra_ObjSetFraig( pObj, 0, pObjNew );
    }
    Extra_ProgressBarStop( pProgress );
p->nClassesEnd = Vec_PtrSize(p->pCla->vClasses) + (int)(Vec_PtrSize(p->pCla->vClasses1) > 0);
    // try to prove the outputs of the miter
    p->nNodesMiter = Aig_ManNodeNum(p->pManFraig);
//    Fra_MiterStatus( p->pManFraig );
//    if ( p->pPars->fProve && p->pManFraig->pData == NULL )
//        Fra_MiterProve( p );
}

/**Function*************************************************************

  Synopsis    [Performs fraiging of the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Fra_FraigPerform( Aig_Man_t * pManAig, Fra_Par_t * pPars )
{
    Fra_Man_t * p;
    Aig_Man_t * pManAigNew;
    int clk;
    if ( Aig_ManNodeNum(pManAig) == 0 )
        return Aig_ManDup(pManAig, 1);
clk = clock();
    assert( Aig_ManLatchNum(pManAig) == 0 );
    p = Fra_ManStart( pManAig, pPars );
    p->pManFraig = Fra_ManPrepareComb( p );
    Fra_Simulate( p, 0 );
    if ( p->pPars->fChoicing )
        Aig_ManReprStart( p->pManFraig, Aig_ManObjIdMax(p->pManAig)+1 );
    Fra_FraigSweep( p );
    Fra_ManFinalizeComb( p );
    if ( p->pPars->fChoicing )
    {
        Fra_ClassesCopyReprs( p->pCla, p->vTimeouts );
        pManAigNew = Aig_ManDupRepr( p->pManAig );
        Aig_ManCreateChoices( pManAigNew );
        Aig_ManStop( p->pManFraig );
        p->pManFraig = NULL;
    }
    else
    {
        Aig_ManCleanup( p->pManFraig );
        pManAigNew = p->pManFraig;
        p->pManFraig = NULL;
    }
p->timeTotal = clock() - clk;
    Fra_ManStop( p );
    return pManAigNew;
}

/**Function*************************************************************

  Synopsis    [Performs choicing of the AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Fra_FraigChoice( Aig_Man_t * pManAig )
{
    Fra_Par_t Pars, * pPars = &Pars; 
    Fra_ParamsDefault( pPars );
    pPars->nBTLimitNode = 1000;
    pPars->fVerbose     = 0;
    pPars->fProve       = 0;
    pPars->fDoSparse    = 1;
    pPars->fSpeculate   = 0;
    pPars->fChoicing    = 1;
    return Fra_FraigPerform( pManAig, pPars );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


