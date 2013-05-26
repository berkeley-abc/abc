/**CFile****************************************************************

  FileName    [abcMfs.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Optimization with don't-cares.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcMfs.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "bool/kit/kit.h"
#include "opt/sfm/sfm.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////
 
////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkAssignIDs( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pObj;
    int i;
    vNodes = Abc_NtkDfs( pNtk, 0 );
    Abc_NtkCleanCopy( pNtk );
    Abc_NtkForEachPi( pNtk, pObj, i )
        pObj->iTemp = i;
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
    {
        pObj->iTemp = Abc_NtkPiNum(pNtk) + i;
//printf( "%d->%d ", pObj->Id, pObj->iTemp );
    }
//printf( "\n" );
    Abc_NtkForEachPo( pNtk, pObj, i )
        pObj->iTemp = Abc_NtkPiNum(pNtk) + Vec_PtrSize(vNodes) + i;
    return vNodes;
}
Vec_Ptr_t * Abc_NtkAssignIDs2( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pObj;
    int i;
    Abc_NtkCleanCopy( pNtk );
    Abc_NtkForEachPi( pNtk, pObj, i )
        pObj->iTemp = i;
    vNodes = Vec_PtrAlloc( Abc_NtkNodeNum(pNtk) );
    Abc_NtkForEachNode( pNtk, pObj, i )
    {
        Vec_PtrPush( vNodes, pObj );
        pObj->iTemp = Abc_NtkPiNum(pNtk) + i;
    }
    Abc_NtkForEachPo( pNtk, pObj, i )
        pObj->iTemp = Abc_NtkPiNum(pNtk) + Vec_PtrSize(vNodes) + i;
    return vNodes;
}

/**Function*************************************************************

  Synopsis    [Extracts information about the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Sfm_Ntk_t * Abc_NtkExtractMfs( Abc_Ntk_t * pNtk, int nFirstFixed )
{
    Vec_Ptr_t * vNodes;
    Vec_Wec_t * vFanins;
    Vec_Str_t * vFixed;
    Vec_Wrd_t * vTruths;
    Vec_Int_t * vArray;
    Abc_Obj_t * pObj, * pFanin;
    int i, k, nObjs;
    vNodes  = nFirstFixed ? Abc_NtkAssignIDs2(pNtk) : Abc_NtkAssignIDs(pNtk);
    nObjs   = Abc_NtkPiNum(pNtk) + Vec_PtrSize(vNodes) + Abc_NtkPoNum(pNtk);
    vFanins = Vec_WecStart( nObjs );
    vFixed  = Vec_StrStart( nObjs );
    vTruths = Vec_WrdStart( nObjs );
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
    {
        vArray = Vec_WecEntry( vFanins, pObj->iTemp );
        Vec_IntGrow( vArray, Abc_ObjFaninNum(pObj) );
        Abc_ObjForEachFanin( pObj, pFanin, k )
            Vec_IntPush( vArray, pFanin->iTemp );
        Vec_WrdWriteEntry( vTruths, pObj->iTemp, Abc_SopToTruth((char *)pObj->pData, Abc_ObjFaninNum(pObj)) );
    }
    Abc_NtkForEachPo( pNtk, pObj, i )
    {
        vArray = Vec_WecEntry( vFanins, pObj->iTemp );
        Vec_IntGrow( vArray, Abc_ObjFaninNum(pObj) );
        Abc_ObjForEachFanin( pObj, pFanin, k )
            Vec_IntPush( vArray, pFanin->iTemp );
    }
    Vec_PtrFree( vNodes );
    // update fixed
    assert( nFirstFixed >= 0 && nFirstFixed < Abc_NtkNodeNum(pNtk) );
    for ( i = Abc_NtkPiNum(pNtk); i < Abc_NtkPiNum(pNtk) + nFirstFixed; i++ )
        Vec_StrWriteEntry( vFixed, i, (char)1 );
    return Sfm_NtkConstruct( vFanins, Abc_NtkPiNum(pNtk), Abc_NtkPoNum(pNtk), vFixed, vTruths );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkInsertMfs( Abc_Ntk_t * pNtk, Sfm_Ntk_t * p )
{
    Vec_Int_t * vCover = Sfm_NodeReadCover(p);
    Vec_Int_t * vMap, * vArray;
    Abc_Obj_t * pNode;
    int i, k, Fanin;
    word * pTruth;
    // map new IDs into old nodes
    vMap = Vec_IntStart( Abc_NtkObjNumMax(pNtk) );
    Abc_NtkForEachPi( pNtk, pNode, i )
        Vec_IntWriteEntry( vMap, pNode->iTemp, Abc_ObjId(pNode) );
    Abc_NtkForEachNode( pNtk, pNode, i )
        if ( pNode->iTemp > 0 )
            Vec_IntWriteEntry( vMap, pNode->iTemp, Abc_ObjId(pNode) );
    // remove old fanins
    Abc_NtkForEachNode( pNtk, pNode, i )
        Abc_ObjRemoveFanins( pNode );
    // create new fanins
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        if ( pNode->iTemp == 0 || Sfm_NodeReadFixed(p, pNode->iTemp) )
            continue;
        if ( !Sfm_NodeReadUsed(p, pNode->iTemp) )
        {
            Abc_NtkDeleteObj( pNode );
            continue;
        }
        // update fanins
        vArray = Sfm_NodeReadFanins( p, pNode->iTemp );
        Vec_IntForEachEntry( vArray, Fanin, k )
            Abc_ObjAddFanin( pNode, Abc_NtkObj(pNtk, Vec_IntEntry(vMap, Fanin)) );
        // update function
        pTruth = Sfm_NodeReadTruth( p, pNode->iTemp );
        if ( pTruth[0] == 0 )
            pNode->pData = Abc_SopRegister( (Mem_Flex_t *)pNtk->pManFunc, " 0\n" );
        else if ( ~pTruth[0] == 0 )
            pNode->pData = Abc_SopRegister( (Mem_Flex_t *)pNtk->pManFunc, " 1\n" );
        else
        {
//            pNode->pData = Abc_SopCreateFromTruth( (Mem_Flex_t *)pNtk->pManFunc, Vec_IntSize(vArray), (unsigned *)pTruth );
            int RetValue = Kit_TruthIsop( (unsigned *)pTruth, Vec_IntSize(vArray), vCover, 1 );
            assert( RetValue == 0 || RetValue == 1 );
            pNode->pData = Abc_SopCreateFromIsop( (Mem_Flex_t *)pNtk->pManFunc, Vec_IntSize(vArray), vCover );
            if ( RetValue )
                Abc_SopComplement( (char *)pNode->pData );
        }
    }
    Vec_IntFree( vMap );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkPerformMfs( Abc_Ntk_t * pNtk, Sfm_Par_t * pPars )
{
    Sfm_Ntk_t * p;
    int nFaninMax, nNodes;
    assert( Abc_NtkIsSopLogic(pNtk) );
    // count fanouts
    nFaninMax = Abc_NtkGetFaninMax( pNtk );
    if ( nFaninMax > 6 )
    {
        Abc_Print( 1, "Currently \"mfs\" cannot process the network containing nodes with more than 6 fanins.\n" );
        return 0;
    }
    // collect information
    p = Abc_NtkExtractMfs( pNtk, pPars->nFirstFixed );
    // perform optimization
    nNodes = Sfm_NtkPerform( p, pPars );
    // call the fast extract procedure
    if ( nNodes == 0 )
        Abc_Print( 1, "The network is not changed by \"mfs\".\n" );
    else
    {
        Abc_NtkInsertMfs( pNtk, p );
        Abc_Print( 1, "The network has %d nodes changed by \"mfs\".\n", nNodes );
    }
    Sfm_NtkFree( p );
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

