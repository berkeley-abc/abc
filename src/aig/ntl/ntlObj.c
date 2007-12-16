/**CFile****************************************************************

  FileName    [.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: .c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntl.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates the primary input.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Obj_t * Ntl_ModelCreatePi( Ntl_Mod_t * pModel )
{
    Ntl_Obj_t * p;
    p = (Ntl_Obj_t *)Aig_MmFlexEntryFetch( pModel->pMan->pMemObjs, sizeof(Ntl_Obj_t) + sizeof(Ntl_Net_t *) );
    memset( p, 0, sizeof(Ntl_Obj_t) + sizeof(Ntl_Net_t *) );
    p->Id = Vec_PtrSize( pModel->vObjs );
    Vec_PtrPush( pModel->vObjs, p );
    Vec_PtrPush( pModel->vPis, p );
    p->pModel   = pModel;
    p->Type     = NTL_OBJ_PI;
    p->nFanins  = 0;
    p->nFanouts = 1;
    pModel->nObjs[NTL_OBJ_PI]++;
    return p;
}

/**Function*************************************************************

  Synopsis    [Creates the primary output.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Obj_t * Ntl_ModelCreatePo( Ntl_Mod_t * pModel, Ntl_Net_t * pNet )
{
    Ntl_Obj_t * p;
    p = (Ntl_Obj_t *)Aig_MmFlexEntryFetch( pModel->pMan->pMemObjs, sizeof(Ntl_Obj_t) + sizeof(Ntl_Net_t *) );
    memset( p, 0, sizeof(Ntl_Obj_t) + sizeof(Ntl_Net_t *) );
    p->Id = Vec_PtrSize( pModel->vObjs );
    Vec_PtrPush( pModel->vObjs, p );
    Vec_PtrPush( pModel->vPos, p );
    p->pModel    = pModel;
    p->Type      = NTL_OBJ_PO;
    p->nFanins   = 1;
    p->nFanouts  = 0;
    p->pFanio[0] = pNet;
    pModel->nObjs[NTL_OBJ_PO]++;
    return p;
}

/**Function*************************************************************

  Synopsis    [Creates the primary output.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Obj_t * Ntl_ModelCreateLatch( Ntl_Mod_t * pModel )
{
    Ntl_Obj_t * p;
    p = (Ntl_Obj_t *)Aig_MmFlexEntryFetch( pModel->pMan->pMemObjs, sizeof(Ntl_Obj_t) + sizeof(Ntl_Net_t *) * 3 );
    memset( p, 0, sizeof(Ntl_Obj_t) + sizeof(Ntl_Net_t *) * 3 );
    p->Id = Vec_PtrSize( pModel->vObjs );
    Vec_PtrPush( pModel->vObjs, p );
    p->pModel   = pModel;
    p->Type     = NTL_OBJ_LATCH;
    p->nFanins  = 2;
    p->nFanouts = 1;
    pModel->nObjs[NTL_OBJ_LATCH]++;
    return p;
}

/**Function*************************************************************

  Synopsis    [Creates the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Obj_t * Ntl_ModelCreateNode( Ntl_Mod_t * pModel, int nFanins )
{
    Ntl_Obj_t * p;
    p = (Ntl_Obj_t *)Aig_MmFlexEntryFetch( pModel->pMan->pMemObjs, sizeof(Ntl_Obj_t) + sizeof(Ntl_Net_t *) * (nFanins + 1) );
    memset( p, 0, sizeof(Ntl_Obj_t) + sizeof(Ntl_Net_t *) * (nFanins + 1) );
    p->Id = Vec_PtrSize( pModel->vObjs );
    Vec_PtrPush( pModel->vObjs, p );
    p->pModel   = pModel;
    p->Type     = NTL_OBJ_NODE;
    p->nFanins  = nFanins;
    p->nFanouts = 1;
    pModel->nObjs[NTL_OBJ_NODE]++;
    return p;
}

/**Function*************************************************************

  Synopsis    [Create the latch.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ntl_Obj_t * Ntl_ModelCreateBox( Ntl_Mod_t * pModel, int nFanins, int nFanouts )
{
    Ntl_Obj_t * p;
    p = (Ntl_Obj_t *)Aig_MmFlexEntryFetch( pModel->pMan->pMemObjs, sizeof(Ntl_Obj_t) + sizeof(Ntl_Net_t *) * (nFanins + nFanouts) );
    memset( p, 0, sizeof(Ntl_Obj_t) + sizeof(Ntl_Net_t *) * (nFanins + nFanouts) );
    p->Id = Vec_PtrSize( pModel->vObjs );
    Vec_PtrPush( pModel->vObjs, p );
    p->pModel   = pModel;
    p->Type     = NTL_OBJ_BOX;
    p->nFanins  = nFanins;
    p->nFanouts = nFanouts;
    pModel->nObjs[NTL_OBJ_BOX]++;
    return p;
}

/**Function*************************************************************

  Synopsis    [Allocates memory and copies the name into it.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Ntl_ManStoreName( Ntl_Man_t * p, char * pName )
{
    char * pStore;
    pStore = Aig_MmFlexEntryFetch( p->pMemObjs, strlen(pName) + 1 );
    strcpy( pStore, pName );
    return pStore;
}

/**Function*************************************************************

  Synopsis    [Allocates memory and copies the SOP into it.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Ntl_ManStoreSop( Ntl_Man_t * p, char * pSop )
{
    char * pStore;
    pStore = Aig_MmFlexEntryFetch( p->pMemSops, strlen(pSop) + 1 );
    strcpy( pStore, pSop );
    return pStore;
}

/**Function*************************************************************

  Synopsis    [Allocates memory and copies the root of file name there.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Ntl_ManStoreFileName( Ntl_Man_t * p, char * pFileName )
{
    char * pBeg, * pEnd, * pStore, * pCur;
    // find the first dot
    for ( pEnd = pFileName; *pEnd; pEnd++ )
        if ( *pEnd == '.' )
            break;
    // find the first char
    for ( pBeg = pEnd - 1; pBeg >= pFileName; pBeg-- )
        if ( !((*pBeg >= 'a' && *pBeg <= 'z') || (*pBeg >= 'A' && *pBeg <= 'Z') || (*pBeg >= '0' && *pBeg <= '9') || *pBeg == '_') )
            break;
    pBeg++;
    // fill up storage
    pStore = Aig_MmFlexEntryFetch( p->pMemSops, pEnd - pBeg + 1 );
    for ( pCur = pStore; pBeg < pEnd; pBeg++, pCur++ )
        *pCur = *pBeg;
    *pCur = 0;
    return pStore;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


