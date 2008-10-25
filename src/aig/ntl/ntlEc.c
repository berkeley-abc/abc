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
    Ntl_Net_t * pNet, * pNext;
    int i, k;
    if ( fSeq )
    {
        Ntl_ModelForEachSeqLeaf( p1, pObj, i )
        {
            Ntl_ObjForEachFanout( pObj, pNext, k )
            {
                pNet = Ntl_ModelFindNet( p2, pNext->pName );
                if ( pNet == NULL )
                    Ntl_ModelCreatePiWithName( p2, pNext->pName );
            }
        }
        Ntl_ModelForEachSeqLeaf( p2, pObj, i )
        {
            Ntl_ObjForEachFanout( pObj, pNext, k )
            {
                pNet = Ntl_ModelFindNet( p1, pNext->pName );
                if ( pNet == NULL )
                    Ntl_ModelCreatePiWithName( p1, pNext->pName );
            }
        }
    }
    else
    {
        Ntl_ModelForEachCombLeaf( p1, pObj, i )
        {
            Ntl_ObjForEachFanout( pObj, pNext, k )
            {
                pNet = Ntl_ModelFindNet( p2, pNext->pName );
                if ( pNet == NULL )
                    Ntl_ModelCreatePiWithName( p2, pNext->pName );
            }
        }
        Ntl_ModelForEachCombLeaf( p2, pObj, i )
        {
            Ntl_ObjForEachFanout( pObj, pNext, k )
            {
                pNet = Ntl_ModelFindNet( p1, pNext->pName );
                if ( pNet == NULL )
                    Ntl_ModelCreatePiWithName( p1, pNext->pName );
            }
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
    Ntl_Net_t * pNet, * pNext;
    int i, k;
    // order the CIs 
    Vec_PtrClear( pMan1->vCis );
    Vec_PtrClear( pMan2->vCis );
    if ( fSeq ) 
    {
        assert( Ntl_ModelSeqLeafNum(p1) == Ntl_ModelSeqLeafNum(p2) );
        Ntl_ModelForEachSeqLeaf( p1, pObj, i )
        {
            Ntl_ObjForEachFanout( pObj, pNext, k )
            {
                pNet = Ntl_ModelFindNet( p2, pNext->pName );
                if ( pNet == NULL )
                {
                    printf( "Ntl_ManDeriveCommonCis(): Internal error!\n" );
                    return;
                }
                Vec_PtrPush( pMan1->vCis, pNext );    
                Vec_PtrPush( pMan2->vCis, pNet );  
            }
        }
    }
    else
    {
        assert( Ntl_ModelCombLeafNum(p1) == Ntl_ModelCombLeafNum(p2) );
        Ntl_ModelForEachCombLeaf( p1, pObj, i )
        {
            Ntl_ObjForEachFanout( pObj, pNext, k )
            {
                pNet = Ntl_ModelFindNet( p2, pNext->pName );
                if ( pNet == NULL )
                {
                    printf( "Ntl_ManDeriveCommonCis(): Internal error!\n" );
                    return;
                }
                Vec_PtrPush( pMan1->vCis, pNext );    
                Vec_PtrPush( pMan2->vCis, pNet );  
            }
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
    Ntl_Net_t * pNet, * pNext;
    int i, k;
    // order the COs 
    Vec_PtrClear( pMan1->vCos );
    Vec_PtrClear( pMan2->vCos );
    if ( fSeq ) 
    {
        Ntl_ModelForEachSeqRoot( p1, pObj, i )
        {
            Ntl_ObjForEachFanin( pObj, pNext, k )
            {
                pNet = Ntl_ModelFindNet( p2, pNext->pName );
                if ( pNet == NULL )
                {
                    printf( "Ntl_ManDeriveCommonCos(): Cannot find output %s in the second design. Skipping it!\n", 
                        pNext->pName );
                    continue;
                }
                Vec_PtrPush( pMan1->vCos, pNext );    
                Vec_PtrPush( pMan2->vCos, pNet );  
            }
        }
    }
    else
    {
        Ntl_ModelForEachCombRoot( p1, pObj, i )
        {
            Ntl_ObjForEachFanin( pObj, pNext, k )
            {
                pNet = Ntl_ModelFindNet( p2, pNext->pName );
                if ( pNet == NULL )
                {
                    printf( "Ntl_ManDeriveCommonCos(): Cannot find output %s in the second design. Skipping it!\n", 
                        pNext->pName );
                    continue;
                }
                Vec_PtrPush( pMan1->vCos, pNext );    
                Vec_PtrPush( pMan2->vCos, pNet );  
            }
        }
    }
}

/**Function*************************************************************

  Synopsis    [Prepares AIGs for combinational equivalence checking.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManPrepareCecMans( Ntl_Man_t * pMan1, Ntl_Man_t * pMan2, Aig_Man_t ** ppAig1, Aig_Man_t ** ppAig2 )
{
    Ntl_Mod_t * pModel1, * pModel2;
    *ppAig1 = NULL;
    *ppAig2 = NULL;
    // make sure they are compatible
    pModel1 = Ntl_ManRootModel( pMan1 );
    pModel2 = Ntl_ManRootModel( pMan2 );
    if ( Ntl_ModelCombLeafNum(pModel1) != Ntl_ModelCombLeafNum(pModel2) )
    {
        printf( "Warning: The number of inputs in the designs is different (%d and %d).\n", 
            Ntl_ModelCombLeafNum(pModel1), Ntl_ModelCombLeafNum(pModel2) );
    }
    if ( Ntl_ModelCombRootNum(pModel1) != Ntl_ModelCombRootNum(pModel2) )
    {
        printf( "Warning: The number of outputs in the designs is different (%d and %d).\n", 
            Ntl_ModelCombRootNum(pModel1), Ntl_ModelCombRootNum(pModel2) );
    }
    // normalize inputs/outputs
    Ntl_ManCreateMissingInputs( pModel1, pModel2, 0 );
    if ( Ntl_ModelCombLeafNum(pModel1) != Ntl_ModelCombLeafNum(pModel2) )
    {
        if ( pMan1 )  Ntl_ManFree( pMan1 );
        if ( pMan2 )  Ntl_ManFree( pMan2 );
        printf( "Ntl_ManPrepareCec(): Cannot verify designs with too many different CIs.\n" );
        return;
    }
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
    *ppAig1 = Ntl_ManCollapse( pMan1, 0 );
    *ppAig2 = Ntl_ManCollapse( pMan2, 0 );
}

/**Function*************************************************************

  Synopsis    [Prepares AIGs for combinational equivalence checking.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ntl_ManPrepareCec( char * pFileName1, char * pFileName2, Aig_Man_t ** ppAig1, Aig_Man_t ** ppAig2 )
{
    Ntl_Man_t * pMan1, * pMan2;
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
    Ntl_ManPrepareCecMans( pMan1, pMan2, ppAig1, ppAig2 );
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
    extern Aig_Man_t * Saig_ManCreateMiter( Aig_Man_t * p1, Aig_Man_t * p2, int Oper );

    Aig_Man_t * pAig1, * pAig2, * pAig;
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
    if ( Ntl_ManLatchNum(pMan1) == 0 || Ntl_ManLatchNum(pMan2) == 0 )
    {
        if ( pMan1 )  Ntl_ManFree( pMan1 );
        if ( pMan2 )  Ntl_ManFree( pMan2 );
        printf( "Ntl_ManPrepareSec(): The designs have no latches. Use combinational command \"*cec\".\n" );
        return NULL;
    }
    pModel1 = Ntl_ManRootModel( pMan1 );
    pModel2 = Ntl_ManRootModel( pMan2 );
    if ( Ntl_ModelSeqLeafNum(pModel1) != Ntl_ModelSeqLeafNum(pModel2) )
    {
        printf( "Warning: The number of inputs in the designs is different (%d and %d).\n", 
            Ntl_ModelPiNum(pModel1), Ntl_ModelPiNum(pModel2) );
    }
    if ( Ntl_ModelSeqRootNum(pModel1) != Ntl_ModelSeqRootNum(pModel2) )
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
    pAig1 = Ntl_ManCollapse( pMan1, 1 );
    pAig2 = Ntl_ManCollapse( pMan2, 1 );
    pAig = Saig_ManCreateMiter( pAig1, pAig2, 0 );
    Aig_ManCleanup( pAig );
    Aig_ManStop( pAig1 );
    Aig_ManStop( pAig2 );
    // cleanup
    Ntl_ManFree( pMan1 );
    Ntl_ManFree( pMan2 );
    return pAig;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


