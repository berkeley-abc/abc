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
#include "ssw.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Remaps representatives of the equivalence classes.]

  Description [For each equivalence class, if the current representative 
  of the class cannot be used because its corresponding net has no-merge 
  attribute, find the topologically-shallowest node, which can be used 
  as a representative.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManUpdateNoMergeReprs( Aig_Man_t * pAig, Aig_Obj_t ** pReprs )
{
    Aig_Obj_t ** pReprsNew = NULL;
    Aig_Obj_t * pObj, * pRepres, * pRepresNew;
    Ntl_Net_t * pNet, * pNetObj;
    int i;

    // allocate room for the new representative
    pReprsNew = ABC_ALLOC( Aig_Obj_t *, Aig_ManObjNumMax(pAig) );
    memset( pReprsNew, 0, sizeof(Aig_Obj_t *) * Aig_ManObjNumMax(pAig) );
    Aig_ManForEachObj( pAig, pObj, i )
    {
        // get the old representative node
        pRepres = pReprs[pObj->Id];
        if ( pRepres == NULL )
            continue;
        // if this representative node is already remapped, skip it
        pRepresNew = pReprsNew[ pRepres->Id ];
        if ( pRepresNew != NULL )
            continue;
        // get the net of the representative node
        pNet = pRepres->pData;
        assert( pRepres->pData != NULL );
        if ( Ntl_ObjIsBox(pNet->pDriver) && pNet->pDriver->pImplem->attrNoMerge )
        {
            // the net belongs to the no-merge box
            pNetObj = pObj->pData;
            if ( Ntl_ObjIsBox(pNetObj->pDriver) && pNetObj->pDriver->pImplem->attrNoMerge )
                continue;
            // the object's net does not belong to the no-merge box
            // pObj can be used instead of pRepres
            pReprsNew[ pRepres->Id ] = pObj;
        }
        else
        {
            // otherwise, it is fine to use pRepres
            pReprsNew[ pRepres->Id ] = pRepres;
        }
    }
    // update the representatives
    Aig_ManForEachObj( pAig, pObj, i )
    {
        // get the representative node
        pRepres = pReprs[ pObj->Id ];
        if ( pRepres == NULL )
            continue;
        // if the representative has no mapping, undo the mapping of the node
        pRepresNew = pReprsNew[ pRepres->Id ];
        if ( pRepresNew == NULL || pRepresNew == pObj )
        {
            pReprs[ pObj->Id ] = NULL;
            continue;
        }
        // remap the representative
//        assert( pObj->Id > pRepresNew->Id );        
//        pReprs[ pObj->Id ] = pRepresNew;
        if ( pObj->Id > pRepresNew->Id )
            pReprs[ pObj->Id ] = pRepresNew;
        else
            pReprs[ pObj->Id ] = NULL;
    }
    ABC_FREE( pReprsNew );
}

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
    pMapBack = ABC_ALLOC( Aig_Obj_t *, Aig_ManObjNumMax(pAigCol) );
    memset( pMapBack, 0, sizeof(Aig_Obj_t *) * Aig_ManObjNumMax(pAigCol) );
    Aig_ManForEachObj( pAig, pObj, i )
    {
        if ( Aig_ObjIsPo(pObj) )
            continue;
        pObjCol = pObj->pData;
        if ( pObjCol == NULL )
            continue;
        if ( pMapBack[pObjCol->Id] == NULL )
            pMapBack[pObjCol->Id] = pObj;
    }

    // create the equivalence classes for the original manager
    pReprs = ABC_ALLOC( Aig_Obj_t *, Aig_ManObjNumMax(pAig) );
    memset( pReprs, 0, sizeof(Aig_Obj_t *) * Aig_ManObjNumMax(pAig) );
    Aig_ManForEachObj( pAig, pObj, i )
    {
        if ( Aig_ObjIsPo(pObj) )
            continue;
        // get the collapsed node
        pObjCol = pObj->pData;
        if ( pObjCol == NULL )
            continue;
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
    ABC_FREE( pMapBack );

    // recall pointers to the nets of pNew
    Aig_ManForEachObj( pAig, pObj, i )
        pObj->pData = pObj->pNext, pObj->pNext = NULL;

    // remap no-merge representatives to point to 
    // the shallowest nodes in the class without no-merge
    Ntl_ManUpdateNoMergeReprs( pAig, pReprs );
    return pReprs;
}

/**Function*************************************************************

  Synopsis    [Uses equivalences in the AIG to reduce the design.]

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
    Ntl_Net_t * pNet, * pNetRepr, * pNetNew;
    Ntl_Mod_t * pRoot;
    Ntl_Obj_t * pNode, * pNodeOld;
    int i, fCompl, Counter = 0;
    char * pNameNew;
//    int Lenght;
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
        // consider special cases, when the net should not be reduced
        if ( Ntl_ObjIsBox(pNet->pDriver) )
        {
            // do not reduce the net if it is driven by a multi-output box
            if ( Ntl_ObjFanoutNum(pNet->pDriver) > 1 )
                continue;
            // do not reduce the net if it has no-merge attribute
            if ( pNet->pDriver->pImplem->attrNoMerge )
                continue;
            // do not reduce the net if the replacement net has no-merge attribute
            if ( pNetRepr != NULL && Ntl_ObjIsBox(pNetRepr->pDriver) && 
                 pNetRepr->pDriver->pImplem->attrNoMerge )
                continue;
        }
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
        pNodeOld = pNet->pDriver;
        if ( !Ntl_ModelClearNetDriver( pNet->pDriver, pNet ) )
            printf( "Ntl_ManReduce(): Internal error! Net already has no driver.\n" );
        if ( !Ntl_ModelSetNetDriver( pNode, pNet ) )
            printf( "Ntl_ManReduce(): Internal error! Net already has a driver.\n" );
/*
        // remove this net from the hash table (but do not remove from the array)
        Ntl_ModelDeleteNet( pRoot, pNet );
        // create new net with the same name
        pNetNew = Ntl_ModelFindOrCreateNet( pRoot, pNet->pName );
        // clean the name
        pNet->pName[0] = 0;
*/
        // create new net with a new name
        pNameNew = Ntl_ModelCreateNetName( pRoot, "noname", (int)(ABC_PTRINT_T)pNet );
        pNetNew = Ntl_ModelFindOrCreateNet( pRoot, pNameNew );

        // make the old node drive the new net without fanouts
        if ( !Ntl_ModelSetNetDriver( pNodeOld, pNetNew ) )
            printf( "Ntl_ManReduce(): Internal error! Net already has a driver.\n" );

        Counter++;
    }
//    printf( "Nets without names = %d.\n", Counter );
}

/**Function*************************************************************

  Synopsis    [Resets complemented attributes of the collapsed AIG.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManResetComplemented( Ntl_Man_t * p, Aig_Man_t * pAigCol )
{
    Ntl_Mod_t * pRoot;
    Ntl_Obj_t * pObj;
    Aig_Obj_t * pObjCol;
    int i;
    pRoot = Ntl_ManRootModel(p);
    Ntl_ModelForEachLatch( pRoot, pObj, i )
    {
        if ( Ntl_ObjIsInit1( pObj ) )
        {
            pObjCol = Ntl_ObjFanout0(pObj)->pCopy;
            assert( pObjCol->fPhase == 0 );
            pObjCol->fPhase = 1;
        }
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
Ntl_Man_t * Ntl_ManFraig( Ntl_Man_t * p, int nPartSize, int nConfLimit, int nLevelMax, int fUseCSat, int fVerbose )
{
    Ntl_Man_t * pNew, * pAux;
    Aig_Man_t * pAig, * pAigCol, * pTemp;

    if ( Ntl_ModelNodeNum(Ntl_ManRootModel(p)) == 0 )
        return Ntl_ManDup(p);

    // collapse the AIG
    pAig = Ntl_ManExtract( p );
    pNew = Ntl_ManInsertAig( p, pAig );
    pAigCol = Ntl_ManCollapseComb( pNew );
    if ( pAigCol == NULL )
    {
        Aig_ManStop( pAig );
        return pNew;
    }

    // perform fraiging for the given design
//    if ( fUseCSat )
    if ( 0 )
    {
        extern Aig_Man_t * Cec_FraigCombinational( Aig_Man_t * pAig, int nConfs, int fVerbose );
        pTemp = Cec_FraigCombinational( pAigCol, nConfLimit, fVerbose );
        Aig_ManStop( pTemp );
    }
    else
    {
        nPartSize = nPartSize? nPartSize : Aig_ManPoNum(pAigCol);
        pTemp = Aig_ManFraigPartitioned( pAigCol, nPartSize, nConfLimit, nLevelMax, fVerbose );
        Aig_ManStop( pTemp );
    }

    // finalize the transformation
    pNew = Ntl_ManFinalize( pAux = pNew, pAig, pAigCol, fVerbose );
    Ntl_ManFree( pAux );
    Aig_ManStop( pAig );
    Aig_ManStop( pAigCol );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Counts the number of resets.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ntl_ManAigCountResets( Ntl_Man_t * pNtl )
{
    Ntl_Mod_t * pModel = Ntl_ManRootModel(pNtl);
    Ntl_Obj_t * pBox;
    int i, Counter = -1;
    Ntl_ModelForEachObj( pModel, pBox, i )
        Counter = ABC_MAX( Counter, pBox->Reset );
    return Counter + 1;
}

/**Function*************************************************************

  Synopsis    [Transforms sequential AIG to allow for async reset.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Ntl_ManAigToRst( Ntl_Man_t * pNtl, Aig_Man_t * p )
{
    Ntl_Mod_t * pModel = Ntl_ManRootModel(pNtl);
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i, iRegNum, iRstNum, Counter = 0;
    int nResets = Ntl_ManAigCountResets( pNtl );
    assert( pNtl->pNal != NULL );
    assert( Aig_ManRegNum(p) > 0 );
    assert( Vec_IntSize(pNtl->vRstClasses) == Aig_ManRegNum(p) );
//printf( "Number of resets before synthesis = %d.\n", nResets );
    // create the PIs
    Aig_ManCleanData( p );
    Aig_ManSetPioNumbers( p );
    // create the new manager
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    pNew->pSpec = Aig_UtilStrsav( p->pSpec );
    // create special PIs
    for ( i = 0; i < nResets; i++ )
        Aig_ObjCreatePi( pNew );
    // duplicate internal nodes
    Aig_ManForEachPi( p, pObj, i )
        pObj->pData = Aig_ObjCreatePi( pNew );
    Aig_ManForEachObj( p, pObj, i )
    {
        if ( Aig_ObjIsNode(pObj) )
            pObj->pData = Aig_And( pNew, Aig_ObjChild0Copy(pObj), Aig_ObjChild1Copy(pObj) );
        else if ( Aig_ObjIsPo(pObj) )
            pObj->pData = Aig_ObjCreatePo( pNew, Aig_ObjChild0Copy(pObj) );
        else if ( Aig_ObjIsPi(pObj) )
        {
//            pObj->pData = Aig_ObjCreatePi( pNew );
            iRegNum = Aig_ObjPioNum(pObj) - (Aig_ManPiNum(p) - Aig_ManRegNum(p));
            if ( iRegNum < 0 )
                continue;
            iRstNum = Vec_IntEntry(pNtl->vRstClasses, iRegNum);
            if ( iRstNum < 0 )
                continue;
            assert( iRstNum < nResets );
            pObj->pData = Aig_And( pNew, pObj->pData, Aig_ManPi(pNew, iRstNum) ); // could be NOT(pi)
            Counter++;
        }
        else if ( Aig_ObjIsConst1(pObj) )
            pObj->pData = Aig_ManConst1(pNew);
        else
            assert( 0 );
    }
    assert( Aig_ManNodeNum(p) + Counter == Aig_ManNodeNum(pNew) );
    if ( (Counter = Aig_ManCleanup( pNew )) )
        printf( "Aig_ManDupOrdered(): Cleanup after AIG duplication removed %d nodes.\n", Counter );
    Aig_ManSetRegNum( pNew, Aig_ManRegNum(p) );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Remaps equivalence classes from the new nodes to the old ones.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManRemapClassesLcorr( Ntl_Man_t * pNtl, Aig_Man_t * p, Aig_Man_t * pNew )
{
    Ntl_Mod_t * pModel = Ntl_ManRootModel(pNtl);
    Aig_Obj_t * pObj, * pObjRepr, * pObjNew, * pObjNewRepr;
    int i, nResets = Ntl_ManAigCountResets( pNtl );
    int nTruePis = Aig_ManPiNum(p) - Aig_ManRegNum(p);
    assert( pNew->pReprs != NULL );
    assert( nResets == Aig_ManPiNum(pNew) - Aig_ManPiNum(p) );
    Aig_ManReprStart( p, Aig_ManObjNumMax(p) );
    Aig_ManForEachLoSeq( pNew, pObjNew, i )
    {
        pObj = Aig_ManPi( p, i - nResets );
        pObjNewRepr = pNew->pReprs[pObjNew->Id];
        if ( pObjNewRepr == NULL )
            continue;
        if ( pObjNewRepr == Aig_ManConst1(pNew) )
        {
            Aig_ObjCreateRepr( p, Aig_ManConst1(p), pObj );
            continue;
        }
        assert( Aig_ObjIsPi(pObjNewRepr) );
        // find the corresponding representative node
        pObjRepr = Aig_ManPi( p, Aig_ObjPioNum(pObjNewRepr) - nResets );
        // if they belong to different domains, quit
        if ( Vec_IntEntry( pNtl->vRstClasses, Aig_ObjPioNum(pObj) - nTruePis ) != 
             Vec_IntEntry( pNtl->vRstClasses, Aig_ObjPioNum(pObjRepr) - nTruePis ) )
            continue;
        Aig_ObjCreateRepr( p, pObjRepr, pObj );
    }
} 

/**Function*************************************************************

  Synopsis    [Remaps equivalence classes from the new nodes to the old ones.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManRemapClassesScorr( Ntl_Man_t * pNtl, Aig_Man_t * p, Aig_Man_t * pNew )
{
    Aig_Obj_t * pObj, * pObjRepr, * pObjNew, * pObjNewRepr;
    int i;
    // map things back
    Aig_ManForEachObj( p, pObj, i )
    {
        pObjNew = pObj->pData;
        assert( pObjNew != NULL && !Aig_IsComplement(pObjNew) );
        pObjNew->pData = pObj;
    }
    // remap the classes
    Aig_ManForEachObj( pNew, pObjNew, i )
    {
        pObjNewRepr = pNew->pReprs[pObjNew->Id];
        if ( pObjNewRepr == NULL )
            continue;
        pObj = pObjNew->pData;
        pObjRepr = pObjNewRepr->pData;    
        assert( Aig_ObjId(pObjRepr) < Aig_ObjId(pObj) );
        Aig_ObjCreateRepr( p, pObjRepr, pObj );
    }
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

    // collapse the AIG
    pAig = Ntl_ManExtract( p );
//Ntl_ManPrintStats( p );
//Aig_ManPrintStats( pAig );
    pNew = Ntl_ManInsertAig( p, pAig );
    pAigCol = Ntl_ManCollapseSeq( pNew, 0, fVerbose );
    if ( pAigCol == NULL )
    {
        Aig_ManStop( pAig );
        return pNew;
    }
//Ntl_ManPrintStats( pNew );
//Aig_ManPrintStats( pAigCol );

    // perform SCL
    if ( p->pNal )
    {
        Aig_Man_t * pAigRst;
        pAigRst = Ntl_ManAigToRst( pNew, pAigCol );
        pTemp = Aig_ManScl( pAigRst, fLatchConst, fLatchEqual, fVerbose );
        Aig_ManStop( pTemp );
        Ntl_ManRemapClassesLcorr( pNew, pAigCol, pAigRst );
        Aig_ManStop( pAigRst );
    }
    else
    {
        pTemp = Aig_ManScl( pAigCol, fLatchConst, fLatchEqual, fVerbose );
        Aig_ManStop( pTemp );
    }

    // finalize the transformation
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
Ntl_Man_t * Ntl_ManLcorr( Ntl_Man_t * p, int nConfMax, int fScorrGia, int fUseCSat, int fVerbose )
{
    Ntl_Man_t * pNew, * pAux;
    Aig_Man_t * pAig, * pAigCol, * pTemp;
    Ssw_Pars_t Pars, * pPars = &Pars;
    Ssw_ManSetDefaultParamsLcorr( pPars );
    pPars->nBTLimit = nConfMax;
    pPars->fVerbose = fVerbose;

    // collapse the AIG
    pAig = Ntl_ManExtract( p );
    pNew = Ntl_ManInsertAig( p, pAig );
    pAigCol = Ntl_ManCollapseSeq( pNew, pPars->nMinDomSize, pPars->fVerbose );
    if ( pAigCol == NULL )
    {
        Aig_ManStop( pAig );
        return pNew;
    }

    // perform LCORR
    pPars->fScorrGia = fScorrGia;
    pPars->fUseCSat  = fUseCSat;
    if ( p->pNal )
    {
        Aig_Man_t * pAigRst;
        pAigRst = Ntl_ManAigToRst( pNew, pAigCol );
        pTemp = Ssw_LatchCorrespondence( pAigRst, pPars );
        Aig_ManStop( pTemp );
        Ntl_ManRemapClassesLcorr( pNew, pAigCol, pAigRst );
        Aig_ManStop( pAigRst );
    }
    else
    {
        pTemp = Ssw_LatchCorrespondence( pAigCol, pPars );
        Aig_ManStop( pTemp );
    }

    // finalize the transformation
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
    assert( 0 ); // not updated for nal

    // collapse the AIG
    pAig = Ntl_ManExtract( p );
    pNew = Ntl_ManInsertAig( p, pAig );
    pAigCol = Ntl_ManCollapseSeq( pNew, pPars->nMinDomSize, pPars->fVerbose );
    if ( pAigCol == NULL )
    {
        Aig_ManStop( pAig );
        return pNew;
    }

    // perform SCL for the given design
    pTemp = Fra_FraigInduction( pAigCol, pPars );
    Aig_ManStop( pTemp );

    // finalize the transformation
    pNew = Ntl_ManFinalize( pAux = pNew, pAig, pAigCol, pPars->fVerbose );
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
Ntl_Man_t * Ntl_ManScorr( Ntl_Man_t * p, Ssw_Pars_t * pPars )
{
    Ntl_Man_t * pNew, * pAux;
    Aig_Man_t * pAig, * pAigCol, * pTemp;

    // collapse the AIG
    pAig = Ntl_ManExtract( p );
    pNew = Ntl_ManInsertAig( p, pAig );
    pAigCol = Ntl_ManCollapseSeq( pNew, pPars->nMinDomSize, pPars->fVerbose );
    if ( pAigCol == NULL )
    {
        Aig_ManStop( pAig );
        return pNew;
    }

    // perform SCL
    if ( p->pNal )
    {
        Aig_Man_t * pAigRst;
        pAigRst = Ntl_ManAigToRst( pNew, pAigCol );
        pTemp = Ssw_SignalCorrespondence( pAigRst, pPars );
        Aig_ManStop( pTemp );
        Ntl_ManRemapClassesLcorr( pNew, pAigCol, pAigRst );
        Aig_ManStop( pAigRst );
    }
    else
    {
        pTemp = Ssw_SignalCorrespondence( pAigCol, pPars );
        Aig_ManStop( pTemp );
    }

    // finalize the transformation
    pNew = Ntl_ManFinalize( pAux = pNew, pAig, pAigCol, pPars->fVerbose );
    Ntl_ManFree( pAux );
    Aig_ManStop( pAig );
    Aig_ManStop( pAigCol );
    return pNew;
}


/**Function*************************************************************

  Synopsis    [Transfers the copy field into the second copy field.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManTransferCopy( Ntl_Man_t * p )
{
    Ntl_Net_t * pNet;
    Ntl_Mod_t * pRoot;
    int i;
    pRoot = Ntl_ManRootModel( p );
    Ntl_ModelForEachNet( pRoot, pNet, i )
    {
        pNet->pCopy2 = pNet->pCopy;
        pNet->pCopy = NULL;
    }
}

/**Function*************************************************************

  Synopsis    [Reattaches one white-box.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManAttachWhiteBox( Ntl_Man_t * p, Aig_Man_t * pAigCol, Aig_Man_t * pAigRed, Ntl_Man_t * pNew, Ntl_Obj_t * pBox )
{
}

/**Function*************************************************************

  Synopsis    [Reattaches white-boxes after reducing the netlist.]

  Description [The following parameters are given:
  Original netlist (p) whose nets point to the nodes of collapsed AIG.
  Collapsed AIG (pAigCol) whose objects point to those of reduced AIG.
  Reduced AIG (pAigRed) whose objects point to the nets of the new netlist.
  The new netlist is changed by this procedure to have those white-boxes
  from the original AIG (p) those outputs are preserved after reduction.
  Note that if outputs are preserved, the inputs are also preserved.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManAttachWhiteBoxes( Ntl_Man_t * p, Aig_Man_t * pAigCol, Aig_Man_t * pAigRed, Ntl_Man_t * pNew, int fVerbose )
{
    Ntl_Mod_t * pRoot;
    Ntl_Obj_t * pBox;
    Ntl_Net_t * pNet;
    int i, k, Counter = 0;
    // go through the white-boxes and check if they are preserved
    pRoot = Ntl_ManRootModel( p );
    Ntl_ModelForEachBox( pRoot, pBox, i )
    {
        Ntl_ObjForEachFanout( pBox, pNet, k )
        {
            // skip dangling outputs of the box
            if ( pNet->pCopy == NULL )
                continue;
            // skip the outputs that are not preserved after merging equivalence
            if ( Aig_Regular(pNet->pCopy2)->pData == NULL )
                continue;
            break;
        }
        if ( k == Ntl_ObjFanoutNum(pBox) )
            continue;
        // the box is preserved
        Ntl_ManAttachWhiteBox( p, pAigCol, pAigRed, pNew, pBox );
        Counter++;
    }
    if ( fVerbose )
        printf( "Attached %d boxed (out of %d).\n", Counter, Ntl_ModelBoxNum(pRoot) );
}

/**Function*************************************************************

  Synopsis    [Flip complemented edges.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManFlipEdges( Ntl_Man_t * p, Aig_Man_t * pAigCol )
{
    Ntl_Mod_t * pRoot;
    Ntl_Obj_t * pObj;
    Aig_Obj_t * pObjCol, * pFanin;
    int i, iLatch;
    pRoot = Ntl_ManRootModel(p);
    iLatch = 0;
    Ntl_ModelForEachLatch( pRoot, pObj, i )
    {
        if ( Ntl_ObjIsInit1( pObj ) )
        {
            pObjCol = Aig_ManPi( pAigCol, Ntl_ModelPiNum(pRoot) + iLatch );
            assert( pObjCol->fMarkA == 0 );
            pObjCol->fMarkA = 1;
        }
        iLatch++;
    }
    // flip pointers to the complemented edges
    Aig_ManForEachObj( pAigCol, pObjCol, i )
    {
        pFanin = Aig_ObjFanin0(pObjCol);
        if ( pFanin && pFanin->fMarkA )
            pObjCol->pFanin0 = Aig_Not(pObjCol->pFanin0);
        pFanin = Aig_ObjFanin1(pObjCol);
        if ( pFanin && pFanin->fMarkA )
            pObjCol->pFanin1 = Aig_Not(pObjCol->pFanin1);
    }
    // flip complemented latch derivers and undo the marks
    iLatch = 0;
    Ntl_ModelForEachLatch( pRoot, pObj, i )
    {
        if ( Ntl_ObjIsInit1( pObj ) )
        {
            // flip the latch input
            pObjCol = Aig_ManPo( pAigCol, Ntl_ModelPoNum(pRoot) + iLatch );
            pObjCol->pFanin0 = Aig_Not(pObjCol->pFanin0);
            // unmark the latch output
            pObjCol = Aig_ManPi( pAigCol, Ntl_ModelPiNum(pRoot) + iLatch );
            assert( pObjCol->fMarkA == 1 );
            pObjCol->fMarkA = 0;
        }
        iLatch++;
    }
}

/**Function*************************************************************

  Synopsis    [Returns AIG with WB after sequential SAT sweeping.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Man_t * Ntl_ManSsw2( Ntl_Man_t * p, Fra_Ssw_t * pPars )
{
    Ntl_Man_t * pNew;
    Aig_Man_t * pAigRed, * pAigCol;
    // collapse the AIG
    pAigCol = Ntl_ManCollapseSeq( p, pPars->nMinDomSize, pPars->fVerbose );
    // transform the collapsed AIG
    pAigRed = Fra_FraigInduction( pAigCol, pPars );
    Aig_ManStop( pAigRed );
    pAigRed = Aig_ManDupReprBasic( pAigCol );
    // insert the result back
    Ntl_ManFlipEdges( p, pAigRed );
    Ntl_ManTransferCopy( p );
    pNew = Ntl_ManInsertAig( p, pAigRed );
    // attach the white-boxes
    Ntl_ManAttachWhiteBoxes( p, pAigCol, pAigRed, pNew, pPars->fVerbose );
    Ntl_ManSweep( pNew, pPars->fVerbose );
    // cleanup
    Aig_ManStop( pAigRed );
    Aig_ManStop( pAigCol );
    return pNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


