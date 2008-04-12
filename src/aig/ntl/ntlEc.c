/**CFile****************************************************************

  FileName    [ntlEc.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Netlist representation.]

  Synopsis    [Equivalence checking procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: ntlEc.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "ntl.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Adds PIs to both models, so that they have the same PIs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManCreateMissingInputs( Ntl_Mod_t * p1, Ntl_Mod_t * p2, int fSeq )
{
    Ntl_Obj_t * pObj;
    Ntl_Net_t * pNet;
    int i;
    Ntl_ModelForEachPi( p1, pObj, i )
    {
        pNet = Ntl_ModelFindNet( p2, Ntl_ObjFanout0(pObj)->pName );
        if ( pNet == NULL )
            Ntl_ModelCreatePiWithName( p2, Ntl_ObjFanout0(pObj)->pName );
    }
    Ntl_ModelForEachPi( p2, pObj, i )
    {
        pNet = Ntl_ModelFindNet( p1, Ntl_ObjFanout0(pObj)->pName );
        if ( pNet == NULL )
            Ntl_ModelCreatePiWithName( p1, Ntl_ObjFanout0(pObj)->pName );
    }
    if ( !fSeq )
    {
        Ntl_ModelForEachLatch( p1, pObj, i )
        {
            pNet = Ntl_ModelFindNet( p2, Ntl_ObjFanout0(pObj)->pName );
            if ( pNet == NULL )
                Ntl_ModelCreatePiWithName( p2, Ntl_ObjFanout0(pObj)->pName );
        }
        Ntl_ModelForEachLatch( p2, pObj, i )
        {
            pNet = Ntl_ModelFindNet( p1, Ntl_ObjFanout0(pObj)->pName );
            if ( pNet == NULL )
                Ntl_ModelCreatePiWithName( p1, Ntl_ObjFanout0(pObj)->pName );
        }
    }
}

/**Function*************************************************************

  Synopsis    [Creates arrays of combinational inputs in the same order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManDeriveCommonCis( Ntl_Man_t * pMan1, Ntl_Man_t * pMan2, int fSeq )
{
    Ntl_Mod_t * p1 = Ntl_ManRootModel(pMan1);
    Ntl_Mod_t * p2 = Ntl_ManRootModel(pMan2);
    Ntl_Obj_t * pObj;
    Ntl_Net_t * pNet;
    int i;
    if ( fSeq )
        assert( Ntl_ModelPiNum(p1) == Ntl_ModelPiNum(p2) );
    else
        assert( Ntl_ModelCiNum(p1) == Ntl_ModelCiNum(p2) );
    // order the CIs 
    Vec_PtrClear( pMan1->vCis );
    Vec_PtrClear( pMan2->vCis );
    Ntl_ModelForEachPi( p1, pObj, i )
    {
        pNet = Ntl_ModelFindNet( p2, Ntl_ObjFanout0(pObj)->pName );
        if ( pNet == NULL )
        {
            printf( "Ntl_ManDeriveCommonCis(): Internal error!\n" );
            return;
        }
        Vec_PtrPush( pMan1->vCis, pObj );    
        Vec_PtrPush( pMan2->vCis, pNet->pDriver );    
    }
    if ( !fSeq )
    {
        Ntl_ModelForEachLatch( p1, pObj, i )
        {
            pNet = Ntl_ModelFindNet( p2, Ntl_ObjFanout0(pObj)->pName );
            if ( pNet == NULL )
            {
                printf( "Ntl_ManDeriveCommonCis(): Internal error!\n" );
                return;
            }
            Vec_PtrPush( pMan1->vCis, pObj );    
            Vec_PtrPush( pMan2->vCis, pNet->pDriver );    
        }
    }
}

/**Function*************************************************************

  Synopsis    [Creates arrays of combinational outputs in the same order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManDeriveCommonCos( Ntl_Man_t * pMan1, Ntl_Man_t * pMan2, int fSeq )
{
    Ntl_Mod_t * p1 = Ntl_ManRootModel(pMan1);
    Ntl_Mod_t * p2 = Ntl_ManRootModel(pMan2);
    Ntl_Obj_t * pObj;
    Ntl_Net_t * pNet;
    int i;
//    if ( fSeq )
//        assert( Ntl_ModelPoNum(p1) == Ntl_ModelPoNum(p2) );
//    else
//        assert( Ntl_ModelCoNum(p1) == Ntl_ModelCoNum(p2) );
    // remember PO in the corresponding net of the second design
    Ntl_ModelForEachPo( p2, pObj, i )
        Ntl_ObjFanin0(pObj)->pCopy = pObj;
    // order the COs 
    Vec_PtrClear( pMan1->vCos );
    Vec_PtrClear( pMan2->vCos );
    Ntl_ModelForEachPo( p1, pObj, i )
    {
        pNet = Ntl_ModelFindNet( p2, Ntl_ObjFanin0(pObj)->pName );
        if ( pNet == NULL )
        {
            printf( "Ntl_ManDeriveCommonCos(): Cannot find output %s in the second design. Skipping it!\n", 
                Ntl_ObjFanin0(pObj)->pName );
            continue;
        }
        Vec_PtrPush( pMan1->vCos, pObj );    
        Vec_PtrPush( pMan2->vCos, pNet->pCopy );    
    }
    if ( !fSeq )
    {
        Ntl_ModelForEachLatch( p2, pObj, i )
            Ntl_ObjFanin0(pObj)->pCopy = pObj;
        Ntl_ModelForEachLatch( p1, pObj, i )
        {
            pNet = Ntl_ModelFindNet( p2, Ntl_ObjFanin0(pObj)->pName );
            if ( pNet == NULL )
            {
                printf( "Ntl_ManDeriveCommonCos(): Cannot find output %s in the second design. Skipping it!\n", 
                    Ntl_ObjFanin0(pObj)->pName );
                continue;
            }
            Vec_PtrPush( pMan1->vCos, pObj );    
            Vec_PtrPush( pMan2->vCos, pNet->pCopy );    
        }
    }
}

/**Function*************************************************************

  Synopsis    [Prepares AIGs for combinational equivalence checking.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManPrepareCec( char * pFileName1, char * pFileName2, Aig_Man_t ** ppMan1, Aig_Man_t ** ppMan2 )
{
    Ntl_Man_t * pMan1, * pMan2;
    Ntl_Mod_t * pModel1, * pModel2;
    *ppMan1 = NULL;
    *ppMan2 = NULL;
    // read the netlists
    pMan1 = Ioa_ReadBlif( pFileName1, 1 );
    pMan2 = Ioa_ReadBlif( pFileName2, 1 );
    if ( !pMan1 || !pMan2 )
    {
        if ( pMan1 )  Ntl_ManFree( pMan1 );
        if ( pMan2 )  Ntl_ManFree( pMan2 );
        printf( "Ntl_ManPrepareCec(): Reading designs from file has failed.\n" );
        return;
    }
    // make sure they are compatible
    pModel1 = Ntl_ManRootModel( pMan1 );
    pModel2 = Ntl_ManRootModel( pMan2 );
    if ( Ntl_ModelCiNum(pModel1) != Ntl_ModelCiNum(pModel2) )
    {
        printf( "Warning: The number of inputs in the designs is different (%d and %d).\n", 
            Ntl_ModelCiNum(pModel1), Ntl_ModelCiNum(pModel2) );
    }
    if ( Ntl_ModelCoNum(pModel1) != Ntl_ModelCoNum(pModel2) )
    {
        printf( "Warning: The number of outputs in the designs is different (%d and %d).\n", 
            Ntl_ModelCoNum(pModel1), Ntl_ModelCoNum(pModel2) );
    }
    // normalize inputs/outputs
    Ntl_ManCreateMissingInputs( pModel1, pModel2, 0 );
    Ntl_ManDeriveCommonCis( pMan1, pMan2, 0 );
    Ntl_ManDeriveCommonCos( pMan1, pMan2, 0 );
    if ( Vec_PtrSize(pMan1->vCos) == 0 )
    {
        printf( "Ntl_ManPrepareCec(): There is no identically-named primary outputs to compare.\n" );
        if ( pMan1 )  Ntl_ManFree( pMan1 );
        if ( pMan2 )  Ntl_ManFree( pMan2 );
        return;
    }
    // derive AIGs
    *ppMan1 = Ntl_ManCollapseForCec( pMan1 );
    *ppMan2 = Ntl_ManCollapseForCec( pMan2 );
    // cleanup
    Ntl_ManFree( pMan1 );
    Ntl_ManFree( pMan2 );
}

/**Function*************************************************************

  Synopsis    [Prepares AIGs for sequential equivalence checking.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Ntl_ManPrepareSec( char * pFileName1, char * pFileName2 )
{
    Aig_Man_t * pAig;
    Ntl_Man_t * pMan1, * pMan2;
    Ntl_Mod_t * pModel1, * pModel2;
    // read the netlists
    pMan1 = Ioa_ReadBlif( pFileName1, 1 );
    pMan2 = Ioa_ReadBlif( pFileName2, 1 );
    if ( !pMan1 || !pMan2 )
    {
        if ( pMan1 )  Ntl_ManFree( pMan1 );
        if ( pMan2 )  Ntl_ManFree( pMan2 );
        printf( "Ntl_ManPrepareSec(): Reading designs from file has failed.\n" );
        return NULL;
    }
    // make sure they are compatible
    pModel1 = Ntl_ManRootModel( pMan1 );
    pModel2 = Ntl_ManRootModel( pMan2 );
    if ( Ntl_ModelLatchNum(pModel1) == 0 || Ntl_ModelLatchNum(pModel2) == 0 )
    {
        if ( pMan1 )  Ntl_ManFree( pMan1 );
        if ( pMan2 )  Ntl_ManFree( pMan2 );
        printf( "Ntl_ManPrepareSec(): The designs have no latches. Use combinational command \"*cec\".\n" );
        return NULL;
    }
    if ( Ntl_ModelPiNum(pModel1) != Ntl_ModelPiNum(pModel2) )
    {
        printf( "Warning: The number of inputs in the designs is different (%d and %d).\n", 
            Ntl_ModelPiNum(pModel1), Ntl_ModelPiNum(pModel2) );
    }
    if ( Ntl_ModelPoNum(pModel1) != Ntl_ModelPoNum(pModel2) )
    {
        printf( "Warning: The number of outputs in the designs is different (%d and %d).\n", 
            Ntl_ModelPoNum(pModel1), Ntl_ModelPoNum(pModel2) );
    }
    // normalize inputs/outputs
    Ntl_ManCreateMissingInputs( pModel1, pModel2, 1 );
    Ntl_ManDeriveCommonCis( pMan1, pMan2, 1 );
    Ntl_ManDeriveCommonCos( pMan1, pMan2, 1 );
    if ( Vec_PtrSize(pMan1->vCos) == 0 )
    {
        printf( "Ntl_ManPrepareSec(): There is no identically-named primary outputs to compare.\n" );
        if ( pMan1 )  Ntl_ManFree( pMan1 );
        if ( pMan2 )  Ntl_ManFree( pMan2 );
        return NULL;
    }
    // derive AIGs
    pAig = Ntl_ManCollapseForSec( pMan1, pMan2 );
    // cleanup
    pMan1->pAig = pMan2->pAig = NULL;
    Ntl_ManFree( pMan1 );
    Ntl_ManFree( pMan2 );
    return pAig;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


