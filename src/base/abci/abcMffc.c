/**CFile****************************************************************

  FileName    [abcMffc.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Computing multi-output maximum fanout-free cones.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcMffc.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

ABC_NAMESPACE_IMPL_START
 
////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Dereferences and collects the nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_MffcDeref_rec( Abc_Obj_t * pNode, Vec_Ptr_t * vNodes )
{
    Abc_Obj_t * pFanin;
    int i;
    if ( Abc_ObjIsCi(pNode) )
        return;
    Abc_ObjForEachFanin( pNode, pFanin, i )
    {
        assert( pFanin->vFanouts.nSize > 0 );
        if ( --pFanin->vFanouts.nSize == 0 )
            Abc_MffcDeref_rec( pFanin, vNodes );
    }
    if ( vNodes )
        Vec_PtrPush( vNodes, pNode );
}

/**Function*************************************************************

  Synopsis    [References the nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_MffcRef_rec( Abc_Obj_t * pNode )
{
    Abc_Obj_t * pFanin;
    int i;
    if ( Abc_ObjIsCi(pNode) )
        return;
    Abc_ObjForEachFanin( pNode, pFanin, i )
    {
        if ( pFanin->vFanouts.nSize++ == 0 )
            Abc_MffcRef_rec( pFanin );
    }
}

/**Function*************************************************************

  Synopsis    [Collects nodes belonging to the MFFC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_MffcCollectNodes( Abc_Obj_t ** pNodes, int nNodes, Vec_Ptr_t * vNodes )
{
    int i;
    Vec_PtrClear( vNodes );
    for ( i = 0; i < nNodes; i++ )
        Abc_MffcDeref_rec( pNodes[i], vNodes );
    for ( i = 0; i < nNodes; i++ )
        Abc_MffcRef_rec( pNodes[i] );
}

/**Function*************************************************************

  Synopsis    [Collects leaves of the MFFC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_MffcCollectLeaves( Vec_Ptr_t * vNodes, Vec_Ptr_t * vLeaves )
{
    Abc_Obj_t * pNode, * pFanin;
    int i, k;
    assert( Vec_PtrSize(vNodes) > 0 );
    pNode = (Abc_Obj_t *)Vec_PtrEntry( vNodes, 0 );
    // label them
    Abc_NtkIncrementTravId( pNode->pNtk );
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pNode, i )
        Abc_NodeSetTravIdCurrent( pNode );
    // collect non-labeled fanins
    Vec_PtrClear( vLeaves );
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pNode, i )
    Abc_ObjForEachFanin( pNode, pFanin, k )
    {
        if ( Abc_NodeIsTravIdCurrent(pFanin) )
            continue;
        Abc_NodeSetTravIdCurrent( pFanin );
        Vec_PtrPush( vLeaves, pFanin );
    }
}

/**Function*************************************************************

  Synopsis    [Collects internal nodes that are roots of MFFCs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NktMffcMarkRoots( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vRoots, * vNodes, * vLeaves;
    Abc_Obj_t * pObj, * pLeaf;
    int i, k;
    Abc_NtkCleanMarkA( pNtk );
    // mark the drivers of combinational outputs
    vRoots  = Vec_PtrAlloc( 1000 );
    Abc_NtkForEachCo( pNtk, pObj, i )
    {
        pObj = Abc_ObjFanin0( pObj );
        if ( Abc_ObjIsCi(pObj) || pObj->fMarkA )
            continue;
        pObj->fMarkA = 1;
        Vec_PtrPush( vRoots, pObj );
    }
    // explore starting from the drivers
    vNodes  = Vec_PtrAlloc( 100 );
    vLeaves = Vec_PtrAlloc( 100 );
    Vec_PtrForEachEntry( Abc_Obj_t *, vRoots, pObj, i )
    {
        // collect internal nodes 
        Abc_MffcCollectNodes( &pObj, 1, vNodes );
        // collect leaves
        Abc_MffcCollectLeaves( vNodes, vLeaves );
        // add non-PI leaves
        Vec_PtrForEachEntry( Abc_Obj_t *, vLeaves, pLeaf, k )
        {
            if ( Abc_ObjIsCi(pLeaf) || pLeaf->fMarkA )
                continue;
            pLeaf->fMarkA = 1;
            Vec_PtrPush( vRoots, pLeaf );
        }
    }
    Vec_PtrFree( vLeaves );
    Vec_PtrFree( vNodes );
    Abc_NtkCleanMarkA( pNtk );
    return vRoots;
}

/**Function*************************************************************

  Synopsis    [Collect fanout reachable root nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NktMffcCollectFanout_rec( Abc_Obj_t * pObj, Vec_Ptr_t * vFanouts )
{
    Abc_Obj_t * pFanout;
    int i;
    if ( Abc_ObjIsCo(pObj) )
        return;
    if ( Abc_ObjFanoutNum(pObj) > 64 )
        return;
    if ( Abc_NodeIsTravIdCurrent(pObj) )
        return;
    Abc_NodeSetTravIdCurrent(pObj);
    if ( pObj->fMarkA )
    {
        if ( pObj->vFanouts.nSize > 0 )
            Vec_PtrPush( vFanouts, pObj );
        return;
    }
    Abc_ObjForEachFanout( pObj, pFanout, i )
        Abc_NktMffcCollectFanout_rec( pFanout, vFanouts );
}

/**Function*************************************************************

  Synopsis    [Collect fanout reachable root nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NktMffcCollectFanout( Abc_Obj_t ** pNodes, int nNodes, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vFanouts )
{
    Abc_Obj_t * pFanin, * pFanout;
    int i, k;
    // dereference nodes
    for ( i = 0; i < nNodes; i++ )
        Abc_MffcDeref_rec( pNodes[i], NULL );
    // collect fanouts
    Vec_PtrClear( vFanouts );
    pFanin = (Abc_Obj_t *)Vec_PtrEntry( vLeaves, 0 );
    Abc_NtkIncrementTravId( pFanin->pNtk );
    Vec_PtrForEachEntry( Abc_Obj_t *, vLeaves, pFanin, i )
        Abc_ObjForEachFanout( pFanin, pFanout, k )
            Abc_NktMffcCollectFanout_rec( pFanout, vFanouts );
    // reference nodes
    for ( i = 0; i < nNodes; i++ )
        Abc_MffcRef_rec( pNodes[i] );
}

/**Function*************************************************************

  Synopsis    [Grow one node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NktMffcGrowOne( Abc_Ntk_t * pNtk, Abc_Obj_t ** ppObjs, int nObjs, Vec_Ptr_t * vNodes, Vec_Ptr_t * vLeaves, Vec_Ptr_t * vFanouts )
{
    Abc_Obj_t * pFanout, * pFanoutBest = NULL;
    double CostBest = 0.0;
    int i, k;
    Abc_MffcCollectNodes( ppObjs, nObjs, vNodes );
    Abc_MffcCollectLeaves( vNodes, vLeaves );
    // collect fanouts of all fanins
    Abc_NktMffcCollectFanout( ppObjs, nObjs, vLeaves, vFanouts );
    // try different fanouts
    Vec_PtrForEachEntry( Abc_Obj_t *, vFanouts, pFanout, i )
    {
        for ( k = 0; k < nObjs; k++ )
            if ( pFanout == ppObjs[k] )
                break;
        if ( k < nObjs )
            continue;
        ppObjs[nObjs] = pFanout;
        Abc_MffcCollectNodes( ppObjs, nObjs+1, vNodes );
        Abc_MffcCollectLeaves( vNodes, vLeaves );
        if ( pFanoutBest == NULL || CostBest < 1.0 * Vec_PtrSize(vNodes)/Vec_PtrSize(vLeaves) ) 
        {
            CostBest = 1.0 * Vec_PtrSize(vNodes)/Vec_PtrSize(vLeaves);
            pFanoutBest = pFanout;
        }
    }
    return pFanoutBest;
}

/**Function*************************************************************

  Synopsis    [Procedure to increase MFF size by pairing nodes.]

  Description [For each node in the array vRoots, find a matching node, 
  so that the ratio of nodes inside to the leaf nodes is maximized.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NktMffcGrowRoots( Abc_Ntk_t * pNtk, Vec_Ptr_t * vRoots )
{
    Vec_Ptr_t * vRoots1, * vNodes, * vLeaves, * vFanouts;
    Abc_Obj_t * pObj, * pRoot2, * pNodes[2];
    int i;
    Abc_NtkCleanMarkA( pNtk );
    Vec_PtrForEachEntry( Abc_Obj_t *, vRoots, pObj, i )
        pObj->fMarkA = 1;
    vRoots1  = Vec_PtrAlloc( 100 );
    vNodes   = Vec_PtrAlloc( 100 );
    vLeaves  = Vec_PtrAlloc( 100 );
    vFanouts = Vec_PtrAlloc( 100 );
    Vec_PtrForEachEntry( Abc_Obj_t *, vRoots, pObj, i )
    {
        pNodes[0] = pObj;
        pRoot2 = Abc_NktMffcGrowOne( pNtk, pNodes, 1, vNodes, vLeaves, vFanouts );
        Vec_PtrPush( vRoots1, pRoot2 );
    }
    Vec_PtrFree( vNodes );
    Vec_PtrFree( vLeaves );
    Vec_PtrFree( vFanouts );
    Abc_NtkCleanMarkA( pNtk );
    return vRoots1;
}

/**Function*************************************************************

  Synopsis    [Procedure to increase MFF size by pairing nodes.]

  Description [For each node in the array vRoots, find a matching node, 
  so that the ratio of nodes inside to the leaf nodes is maximized.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NktMffcGrowRootsAgain( Abc_Ntk_t * pNtk, Vec_Ptr_t * vRoots, Vec_Ptr_t * vRoots1 )
{
    Vec_Ptr_t * vRoots2, * vNodes, * vLeaves, * vFanouts;
    Abc_Obj_t * pObj, * pRoot2, * ppObjs[3];
    int i;
    Abc_NtkCleanMarkA( pNtk );
    Vec_PtrForEachEntry( Abc_Obj_t *, vRoots, pObj, i )
        pObj->fMarkA = 1;
    vRoots2  = Vec_PtrAlloc( 100 );
    vNodes   = Vec_PtrAlloc( 100 );
    vLeaves  = Vec_PtrAlloc( 100 );
    vFanouts = Vec_PtrAlloc( 100 );
    Vec_PtrForEachEntry( Abc_Obj_t *, vRoots, pObj, i )
    {
        ppObjs[0] = pObj;
        ppObjs[1] = (Abc_Obj_t *)Vec_PtrEntry( vRoots1, i );
        if ( ppObjs[1] == NULL )
        {
            Vec_PtrPush( vRoots2, NULL );
            continue;
        }
        pRoot2    = Abc_NktMffcGrowOne( pNtk, ppObjs, 2, vNodes, vLeaves, vFanouts );
        Vec_PtrPush( vRoots2, pRoot2 );
    }
    Vec_PtrFree( vNodes );
    Vec_PtrFree( vLeaves );
    Vec_PtrFree( vFanouts );
    Abc_NtkCleanMarkA( pNtk );
    assert( Vec_PtrSize(vRoots) == Vec_PtrSize(vRoots2) );
    return vRoots2;
}

/**Function*************************************************************

  Synopsis    [Testbench.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NktMffcPrint( char * pFileName, Abc_Obj_t ** pNodes, int nNodes, Vec_Ptr_t * vNodes, Vec_Ptr_t * vLeaves )
{
    FILE * pFile;
    Abc_Obj_t * pObj, * pFanin;
    int i, k;
    // convert the network
    Abc_NtkToSop( pNodes[0]->pNtk, 0 );
    // write the file
    pFile = fopen( pFileName, "wb" );
    fprintf( pFile, ".model %s_part\n", pNodes[0]->pNtk->pName );
    fprintf( pFile, ".inputs" );
    Vec_PtrForEachEntry( Abc_Obj_t *, vLeaves, pObj, i )
        fprintf( pFile, " %s", Abc_ObjName(pObj) );
    fprintf( pFile, "\n" );
    fprintf( pFile, ".outputs" );
    for ( i = 0; i < nNodes; i++ )
        fprintf( pFile, " %s", Abc_ObjName(pNodes[i]) );
    fprintf( pFile, "\n" );
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pObj, i )
    {
        fprintf( pFile, ".names" );
        Abc_ObjForEachFanin( pObj, pFanin, k )
            fprintf( pFile, " %s", Abc_ObjName(pFanin) );
        fprintf( pFile, " %s", Abc_ObjName(pObj) );
        fprintf( pFile, "\n%s", (char *)pObj->pData );
    }
    fprintf( pFile, ".end\n" );
    fclose( pFile );
}

/**Function*************************************************************

  Synopsis    [Testbench.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NktMffcTest( Abc_Ntk_t * pNtk )
{
    char pFileName[1000];
    Vec_Ptr_t * vRoots, * vRoots1, * vRoots2, * vNodes, * vLeaves;
    Abc_Obj_t * pNodes[3], * pObj;
    int i, nNodes = 0, nNodes2 = 0;
    vRoots  = Abc_NktMffcMarkRoots( pNtk );
    vRoots1 = Abc_NktMffcGrowRoots( pNtk, vRoots );
    vRoots2 = Abc_NktMffcGrowRootsAgain( pNtk, vRoots, vRoots1 );
    vNodes  = Vec_PtrAlloc( 100 );
    vLeaves = Vec_PtrAlloc( 100 );
    Vec_PtrForEachEntry( Abc_Obj_t *, vRoots, pObj, i )
    {
        printf( "%6d : ",      i );

        Abc_MffcCollectNodes( &pObj, 1, vNodes );
        Abc_MffcCollectLeaves( vNodes, vLeaves );
        nNodes += Vec_PtrSize(vNodes);
        printf( "%6d  ",      Abc_ObjId(pObj) );
        printf( "Vol =%3d  ", Vec_PtrSize(vNodes) );
        printf( "Cut =%3d  ", Vec_PtrSize(vLeaves) );
        if ( Vec_PtrSize(vLeaves) < 2 )
        {
            printf( "\n" );
            continue;
        }

        pNodes[0] = pObj;
        pNodes[1] = (Abc_Obj_t *)Vec_PtrEntry( vRoots1, i );
        pNodes[2] = (Abc_Obj_t *)Vec_PtrEntry( vRoots2, i );
        if ( pNodes[1] == NULL || pNodes[2] == NULL )
        {
            printf( "\n" );
            continue;
        }
        Abc_MffcCollectNodes( pNodes, 3, vNodes );
        Abc_MffcCollectLeaves( vNodes, vLeaves );
        nNodes2 += Vec_PtrSize(vNodes);
        printf( "%6d  ",      Abc_ObjId(pNodes[1]) );
        printf( "%6d  ",      Abc_ObjId(pNodes[2]) );
        printf( "Vol =%3d  ", Vec_PtrSize(vNodes) );
        printf( "Cut =%3d  ", Vec_PtrSize(vLeaves) );
 
        printf( "%4.2f  ",    1.0 * Vec_PtrSize(vNodes)/Vec_PtrSize(vLeaves)  );
        printf( "\n" );

        // generate file
        if ( Vec_PtrSize(vNodes) < 10 )
            continue;
        sprintf( pFileName, "%s_mffc%04d_%02d.blif", Abc_NtkName(pNtk), Abc_ObjId(pObj), Vec_PtrSize(vNodes) );
        Abc_NktMffcPrint( pFileName, pNodes, 3, vNodes, vLeaves );
    }
    printf( "Total nodes = %d.  Root nodes = %d.  Mffc nodes = %d.  Mffc nodes2 = %d.\n", 
        Abc_NtkNodeNum(pNtk), Vec_PtrSize(vRoots), nNodes, nNodes2 );
    Vec_PtrFree( vNodes );
    Vec_PtrFree( vLeaves );
    Vec_PtrFree( vRoots );
    Vec_PtrFree( vRoots1 );
    Vec_PtrFree( vRoots2 );
}


ABC_NAMESPACE_IMPL_END

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


