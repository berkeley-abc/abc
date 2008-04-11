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

    // map the AIG managers
    Aig_ManForEachObj( pAig, pObj, i )
        if ( Aig_ObjIsConst1(pObj) )
            pObj->pData = Aig_ManConst1(pAigCol);
        else if ( !Aig_ObjIsPo(pObj) )
        {
            pNet = pObj->pData;
            pObjCol = Aig_Regular(pNet->pCopy);
            pObj->pData = pObjCol;
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
    return pReprs;
}

/**Function*************************************************************

  Synopsis    [Returns AIG with WB after fraiging.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Ntl_ManFraig( Ntl_Man_t * p, Aig_Man_t * pAig, int nPartSize, int nConfLimit, int nLevelMax, int fVerbose )
{
    Ntl_Man_t * pNew;
    Aig_Man_t * pAigCol, * pTemp;
    assert( pAig->pReprs == NULL );

    // create a new netlist whose nodes are in 1-to-1 relationship with AIG
    pNew = Ntl_ManInsertAig( p, pAig );
    if ( pNew == NULL )
    {
        printf( "Ntk_ManFraig(): Inserting AIG has failed.\n" );
        return NULL;
    }

    // collapse the AIG
    pAigCol = Ntl_ManCollapse( pNew, 0 );
    // perform fraiging for the given design
    if ( nPartSize == 0 )
        nPartSize = Aig_ManPoNum(pAigCol);
    pTemp = Aig_ManFraigPartitioned( pAigCol, nPartSize, nConfLimit, nLevelMax, fVerbose );
    Aig_ManStop( pTemp );

    // transfer equivalence classes to the original AIG
    pAig->pReprs = Ntl_ManFraigDeriveClasses( pAig, pNew, pAigCol );
    pAig->nReprsAlloc = Aig_ManObjNumMax(pAig);
    // cleanup
    Aig_ManStop( pAigCol );
    Ntl_ManFree( pNew );

    // derive the new AIG
    pTemp = Aig_ManDupRepresDfs( pAig );
    // duplicate the timing manager
    if ( pAig->pManTime )
        pTemp->pManTime = Tim_ManDup( pAig->pManTime, 0 );
    // reset levels
    Aig_ManChoiceLevel( pTemp );
    return pTemp;
}

/**Function*************************************************************

  Synopsis    [Performs sequential cleanup.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Ntl_ManScl( Ntl_Man_t * p, Aig_Man_t * pAig, int fLatchConst, int fLatchEqual, int fVerbose )
{
    Ntl_Man_t * pNew;
    Aig_Man_t * pAigCol, * pTemp;
    assert( pAig->pReprs == NULL );

    // create a new netlist whose nodes are in 1-to-1 relationship with AIG
    pNew = Ntl_ManInsertAig( p, pAig );
    if ( pNew == NULL )
    {
        printf( "Ntk_ManFraig(): Inserting AIG has failed.\n" );
        return NULL;
    }
 
    // collapse the AIG
    pAigCol = Ntl_ManCollapse( pNew, 1 );
    // perform fraiging for the given design
    pAigCol->nRegs = Ntl_ModelLatchNum(Ntl_ManRootModel(p));
    pTemp = Aig_ManScl( pAigCol, fLatchConst, fLatchEqual, fVerbose );
    Aig_ManStop( pTemp );

    // transfer equivalence classes to the original AIG
    pAig->pReprs = Ntl_ManFraigDeriveClasses( pAig, pNew, pAigCol );
    pAig->nReprsAlloc = Aig_ManObjNumMax(pAig);
    // cleanup
    Aig_ManStop( pAigCol );
    Ntl_ManFree( pNew );

    // derive the new AIG
    pTemp = Aig_ManDupRepresDfs( pAig );
printf( "Intermediate:\n" );
Aig_ManPrintStats( pTemp );
    // duplicate the timing manager
    if ( pAig->pManTime )
        pTemp->pManTime = Tim_ManDup( pAig->pManTime, 0 );
    // reset levels
    Aig_ManChoiceLevel( pTemp );
    return pTemp;
}

/**Function*************************************************************

  Synopsis    [Returns AIG with WB after fraiging.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Ntl_ManLcorr( Ntl_Man_t * p, Aig_Man_t * pAig, int nConfMax, int fVerbose )
{
    Ntl_Man_t * pNew;
    Aig_Man_t * pAigCol, * pTemp;
    assert( pAig->pReprs == NULL );

    // create a new netlist whose nodes are in 1-to-1 relationship with AIG
    pNew = Ntl_ManInsertAig( p, pAig );
    if ( pNew == NULL )
    {
        printf( "Ntk_ManFraig(): Inserting AIG has failed.\n" );
        return NULL;
    }

    // collapse the AIG
    pAigCol = Ntl_ManCollapse( pNew, 1 );
    // perform fraiging for the given design
    pAigCol->nRegs = Ntl_ModelLatchNum(Ntl_ManRootModel(p));
    pTemp = Fra_FraigLatchCorrespondence( pAigCol, 0, nConfMax, 0, fVerbose, NULL );
//printf( "Reprs = %d.\n", Aig_ManCountReprs(pAigCol) );
    Aig_ManStop( pTemp );

    // transfer equivalence classes to the original AIG
    pAig->pReprs = Ntl_ManFraigDeriveClasses( pAig, pNew, pAigCol );
    pAig->nReprsAlloc = Aig_ManObjNumMax(pAig);
//printf( "Reprs = %d.\n", Aig_ManCountReprs(pAig) );
    // cleanup
    Aig_ManStop( pAigCol );
    Ntl_ManFree( pNew );

    // derive the new AIG
    pTemp = Aig_ManDupRepresDfs( pAig );
//printf( "Intermediate LCORR:\n" );
//Aig_ManPrintStats( pTemp );
    // duplicate the timing manager
    if ( pAig->pManTime )
        pTemp->pManTime = Tim_ManDup( pAig->pManTime, 0 );
    // reset levels
    Aig_ManChoiceLevel( pTemp );
    return pTemp;
}

/**Function*************************************************************

  Synopsis    [Returns AIG with WB after fraiging.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Ntl_ManSsw( Ntl_Man_t * p, Aig_Man_t * pAig, Fra_Ssw_t * pPars )
{
    Ntl_Man_t * pNew;
    Aig_Man_t * pAigCol, * pTemp;
    assert( pAig->pReprs == NULL );

    // create a new netlist whose nodes are in 1-to-1 relationship with AIG
    pNew = Ntl_ManInsertAig( p, pAig );
    if ( pNew == NULL )
    {
        printf( "Ntk_ManFraig(): Inserting AIG has failed.\n" );
        return NULL;
    }

    // collapse the AIG
    pAigCol = Ntl_ManCollapse( pNew, 1 );
    // perform fraiging for the given design
    pAigCol->nRegs = Ntl_ModelLatchNum(Ntl_ManRootModel(p));
    pTemp = Fra_FraigInduction( pAigCol, pPars );
    Aig_ManStop( pTemp );

    // transfer equivalence classes to the original AIG
    pAig->pReprs = Ntl_ManFraigDeriveClasses( pAig, pNew, pAigCol );
    pAig->nReprsAlloc = Aig_ManObjNumMax(pAig);
    // cleanup
    Aig_ManStop( pAigCol );
    Ntl_ManFree( pNew );

    // derive the new AIG
    pTemp = Aig_ManDupRepresDfs( pAig );
    // duplicate the timing manager
    if ( pAig->pManTime )
        pTemp->pManTime = Tim_ManDup( pAig->pManTime, 0 );
    // reset levels
    Aig_ManChoiceLevel( pTemp );
    return pTemp;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


