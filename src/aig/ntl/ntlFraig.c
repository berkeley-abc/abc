/**CFile****************************************************************

  FileName    [ntlFraig.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Performing fraiging with white-boxes.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntlFraig.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntl.h"
#include "fra.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Transfers equivalence class info from pAigCol to pAig.]

  Description [pAig points to the nodes of netlist (pNew) derived using it.
  pNew points to the nodes of the collapsed AIG (pAigCol) derived using it.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t ** Ntl_ManFraigDeriveClasses( Aig_Man_t * pAig, Ntl_Man_t * pNew, Aig_Man_t * pAigCol )
{
    Ntl_Net_t * pNet;
    Aig_Obj_t ** pReprs = NULL, ** pMapBack = NULL;
    Aig_Obj_t * pObj, * pObjCol, * pObjColRepr, * pCorresp;
    int i;

    // remember pointers to the nets of pNew
    Aig_ManForEachObj( pAig, pObj, i )
        pObj->pNext = pObj->pData;

    // map the AIG managers
    Aig_ManForEachObj( pAig, pObj, i )
    {
        if ( Aig_ObjIsConst1(pObj) )
            pObj->pData = Aig_ManConst1(pAigCol);
        else if ( !Aig_ObjIsPo(pObj) )
        {
            pNet = pObj->pData;
            pObjCol = Aig_Regular(pNet->pCopy);
            pObj->pData = pObjCol;
        }
    }

    // create mapping from the collapsed manager into the original manager
    // (each node in the collapsed manager may have more than one equivalent node 
    // in the original manager; this procedure finds the first node in the original 
    // manager that is equivalent to the given node in the collapsed manager) 
    pMapBack = ALLOC( Aig_Obj_t *, Aig_ManObjNumMax(pAigCol) );
    memset( pMapBack, 0, sizeof(Aig_Obj_t *) * Aig_ManObjNumMax(pAigCol) );
    Aig_ManForEachObj( pAig, pObj, i )
    {
        if ( Aig_ObjIsPo(pObj) )
            continue;
        pObjCol = pObj->pData;
        if ( pMapBack[pObjCol->Id] == NULL )
            pMapBack[pObjCol->Id] = pObj;
    }

    // create the equivalence classes for the original manager
    pReprs = ALLOC( Aig_Obj_t *, Aig_ManObjNumMax(pAig) );
    memset( pReprs, 0, sizeof(Aig_Obj_t *) * Aig_ManObjNumMax(pAig) );
    Aig_ManForEachObj( pAig, pObj, i )
    {
        if ( Aig_ObjIsPo(pObj) )
            continue;
        // get the collapsed node
        pObjCol = pObj->pData;
        // get the representative of the collapsed node
        pObjColRepr = pAigCol->pReprs[pObjCol->Id];
        if ( pObjColRepr == NULL )
            pObjColRepr = pObjCol;
        // get the corresponding original node
        pCorresp = pMapBack[pObjColRepr->Id];
        if ( pCorresp == NULL || pCorresp == pObj )
            continue;
        // set the representative
        if ( pCorresp->Id < pObj->Id )
            pReprs[pObj->Id] = pCorresp;
        else
            pReprs[pCorresp->Id] = pObj;
    }
    free( pMapBack );

    // recall pointers to the nets of pNew
    Aig_ManForEachObj( pAig, pObj, i )
        pObj->pData = pObj->pNext, pObj->pNext = NULL;
    return pReprs;
}

/**Function*************************************************************

  Synopsis    [Uses equivalences in the AID to reduce the design.]

  Description [The AIG (pAig) was extracted from the netlist and still 
  points to it (pObj->pData is the pointer to the nets in the netlist).
  Equivalences have been computed for the collapsed AIG and transfered
  to this AIG (pAig). This procedure reduces the corresponding nets.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManReduce( Ntl_Man_t * p, Aig_Man_t * pAig )
{
    Aig_Obj_t * pObj, * pObjRepr;
    Ntl_Net_t * pNet, * pNetRepr;
    Ntl_Mod_t * pRoot;
    Ntl_Obj_t * pNode;
    int i, fCompl, Counter = 0;
    assert( pAig->pReprs );
    pRoot = Ntl_ManRootModel( p );

    Aig_ManForEachObj( pAig, pObj, i )
    {
        pObjRepr = Aig_ObjRepr( pAig, pObj );
        if ( pObjRepr == NULL )
            continue;
        assert( pObj != pObjRepr );
        pNet = pObj->pData;
        pNetRepr = pObjRepr->pData;
        if ( pNetRepr == NULL )
        {
            // this is the constant node
            assert( Aig_ObjIsConst1(pObjRepr) );
            pNode = Ntl_ModelCreateNode( pRoot, 0 );
            pNode->pSop = Ntl_ManStoreSop( p->pMemSops, " 1\n" );
            if ( (pNetRepr = Ntl_ModelFindNet( pRoot, "Const1" )) )
            {
                printf( "Ntl_ManReduce(): Internal error: Intermediate net name is not unique.\n" );
                return;
            }
            pNetRepr = Ntl_ModelFindOrCreateNet( pRoot, "Const1" );
            if ( !Ntl_ModelSetNetDriver( pNode, pNetRepr ) )
            {
                printf( "Ntl_ManReduce(): Internal error: Net has more than one fanin.\n" );
                return;
            }
            pObjRepr->pData = pNetRepr;
            pNetRepr->pCopy = Aig_ManConst1(pAig);
        }
        // get the complemented attributes of the nets
        fCompl = Aig_IsComplement(pNet->pCopy) ^ Aig_Regular(pNet->pCopy)->fPhase ^
                 Aig_IsComplement(pNetRepr->pCopy) ^ Aig_Regular(pNetRepr->pCopy)->fPhase;
        // create interter/buffer driven by the representative net
        pNode = Ntl_ModelCreateNode( pRoot, 1 );
        pNode->pSop = fCompl? Ntl_ManStoreSop( p->pMemSops, "0 1\n" ) : Ntl_ManStoreSop( p->pMemSops, "1 1\n" );
        Ntl_ObjSetFanin( pNode, pNetRepr, 0 );
        // make the new node drive the equivalent net (pNet)
        if ( !Ntl_ModelClearNetDriver( pNet->pDriver, pNet ) )
            printf( "Ntl_ManReduce(): Internal error! Net already has no driver.\n" );
        if ( !Ntl_ModelSetNetDriver( pNode, pNet ) )
            printf( "Ntl_ManReduce(): Internal error! Net already has a driver.\n" );
        Counter++;
    }
}

/**Function*************************************************************

  Synopsis    [Finalizes the transformation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Man_t * Ntl_ManFinalize( Ntl_Man_t * pNew, Aig_Man_t * pAig, Aig_Man_t * pAigCol, int fVerbose )
{
    int fUseExtraSweep = 1;
    Ntl_Man_t * pSwept;
    Aig_Man_t * pTemp;
    assert( pAig->pReprs == NULL );
    assert( pAigCol->pReprs != NULL );

    // transfer equivalence classes to the original AIG
    pAig->pReprs = Ntl_ManFraigDeriveClasses( pAig, pNew, pAigCol );
    pAig->nReprsAlloc = Aig_ManObjNumMax(pAig);
if ( fVerbose )
    printf( "Equivalences:  Collapsed = %5d.  Extracted = %5d.\n", Aig_ManCountReprs(pAigCol), Aig_ManCountReprs(pAig) );

    // implement equivalence classes and remove dangling nodes
    Ntl_ManReduce( pNew, pAig );
    Ntl_ManSweep( pNew, fVerbose );

    // perform one more sweep
    if ( fUseExtraSweep )
    {
        pTemp = Ntl_ManExtract( pNew );
        pSwept = Ntl_ManInsertAig( pNew, pTemp );
        Aig_ManStop( pTemp );
        Ntl_ManSweep( pSwept, fVerbose );
        return pSwept;
    }
    return Ntl_ManDup(pNew);
}

/**Function*************************************************************

  Synopsis    [Returns AIG with WB after fraiging.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Man_t * Ntl_ManFraig( Ntl_Man_t * p, int nPartSize, int nConfLimit, int nLevelMax, int fVerbose )
{
    Ntl_Man_t * pNew, * pAux;
    Aig_Man_t * pAig, * pAigCol, * pTemp;

    // collapse the AIG
    pAig = Ntl_ManExtract( p );
    pNew = Ntl_ManInsertAig( p, pAig );
    pAigCol = Ntl_ManCollapse( pNew );

    // perform fraiging for the given design
    nPartSize = nPartSize? nPartSize : Aig_ManPoNum(pAigCol);
    pTemp = Aig_ManFraigPartitioned( pAigCol, nPartSize, nConfLimit, nLevelMax, fVerbose );
    Aig_ManStop( pTemp );

    // finalize the transformatoin
    pNew = Ntl_ManFinalize( pAux = pNew, pAig, pAigCol, fVerbose );
    Ntl_ManFree( pAux );
    Aig_ManStop( pAig );
    Aig_ManStop( pAigCol );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Performs sequential cleanup.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Man_t * Ntl_ManScl( Ntl_Man_t * p, int fLatchConst, int fLatchEqual, int fVerbose )
{
    Ntl_Man_t * pNew, * pAux;
    Aig_Man_t * pAig, * pAigCol, * pTemp;

    // transform the design
    Ntl_ManTransformInitValues( p );

    // collapse the AIG
    pAig = Ntl_ManExtract( p );
    pNew = Ntl_ManInsertAig( p, pAig );
    pAigCol = Ntl_ManCollapse( pNew );

    // perform SCL for the given design
    pAigCol->nRegs = Ntl_ModelLatchNum(Ntl_ManRootModel(p));
    pTemp = Aig_ManScl( pAigCol, fLatchConst, fLatchEqual, fVerbose );
    Aig_ManStop( pTemp );

    // finalize the transformatoin
    pNew = Ntl_ManFinalize( pAux = pNew, pAig, pAigCol, fVerbose );
    Ntl_ManFree( pAux );
    Aig_ManStop( pAig );
    Aig_ManStop( pAigCol );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Returns AIG with WB after fraiging.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Man_t * Ntl_ManLcorr( Ntl_Man_t * p, int nConfMax, int fVerbose )
{
    Ntl_Man_t * pNew, * pAux;
    Aig_Man_t * pAig, * pAigCol, * pTemp;

    // transform the design
    Ntl_ManTransformInitValues( p );

    // collapse the AIG
    pAig = Ntl_ManExtract( p );
    pNew = Ntl_ManInsertAig( p, pAig );
    pAigCol = Ntl_ManCollapse( pNew );

    // perform SCL for the given design
    pAigCol->nRegs = Ntl_ModelLatchNum(Ntl_ManRootModel(p));
    pTemp = Fra_FraigLatchCorrespondence( pAigCol, 0, nConfMax, 0, fVerbose, NULL );
    Aig_ManStop( pTemp );

    // finalize the transformatoin
    pNew = Ntl_ManFinalize( pAux = pNew, pAig, pAigCol, fVerbose );
    Ntl_ManFree( pAux );
    Aig_ManStop( pAig );
    Aig_ManStop( pAigCol );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Returns AIG with WB after fraiging.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Man_t * Ntl_ManSsw( Ntl_Man_t * p, Fra_Ssw_t * pPars )
{
    Ntl_Man_t * pNew, * pAux;
    Aig_Man_t * pAig, * pAigCol, * pTemp;

    // transform the design
    Ntl_ManTransformInitValues( p );

    // collapse the AIG
    pAig = Ntl_ManExtract( p );
    pNew = Ntl_ManInsertAig( p, pAig );
    pAigCol = Ntl_ManCollapse( pNew );

    // perform SCL for the given design
    pAigCol->nRegs = Ntl_ModelLatchNum(Ntl_ManRootModel(p));
    pTemp = Fra_FraigInduction( pAigCol, pPars );
    Aig_ManStop( pTemp );

    // finalize the transformatoin
    pNew = Ntl_ManFinalize( pAux = pNew, pAig, pAigCol, pPars->fVerbose );
    Ntl_ManFree( pAux );
    Aig_ManStop( pAig );
    Aig_ManStop( pAigCol );
    return pNew;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


