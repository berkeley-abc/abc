/**CFile****************************************************************

  FileName    [abcFanOrder.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Fanin ordering procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcFanOrder.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

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

  Synopsis    [Reorder fanins of the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkOrderFaninsById( Abc_Ntk_t * pNtk )
{
    Vec_Int_t * vOrder;
    Vec_Str_t * vStore;
    Abc_Obj_t * pNode;
    char * pSop, * pSopNew;
    char * pCube, * pCubeNew;
    int nVars, i, v, * pOrder;
    assert( Abc_NtkIsSopLogic(pNtk) );
    vOrder = Vec_IntAlloc( 100 );
    vStore = Vec_StrAlloc( 100 );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        pSop = (char *)pNode->pData;
        nVars = Abc_SopGetVarNum(pSop);
        assert( nVars == Abc_ObjFaninNum(pNode) );
        Vec_IntClear( vOrder );
        for ( v = 0; v < nVars; v++ )
            Vec_IntPush( vOrder, v );
        pOrder = Vec_IntArray(vOrder);
        Vec_IntSelectSortCost( pOrder, nVars, &pNode->vFanins );
        // copy the cover
        Vec_StrGrow( vStore, Abc_SopGetCubeNum(pSop) * (nVars + 3) + 1 );
        memcpy( Vec_StrArray(vStore), pSop, Abc_SopGetCubeNum(pSop) * (nVars + 3) + 1 );
        pSopNew = pCubeNew = pSop;
        pSop = Vec_StrArray(vStore);
        // generate permuted one
        Abc_SopForEachCube( pSop, nVars, pCube )
        {
            for ( v = 0; v < nVars; v++ )
                pCubeNew[v] = '-';
            for ( v = 0; v < nVars; v++ )
                if ( pCube[pOrder[v]] == '0' )
                    pCubeNew[v] = '0';
                else if ( pCube[pOrder[v]] == '1' )
                    pCubeNew[v] = '1';
            pCubeNew += nVars + 3;
        }
        pNode->pData = pSopNew;
        Vec_IntSort( &pNode->vFanins, 0 );
//        Vec_IntPrint( vOrder );
    }
    Vec_IntFree( vOrder );
    Vec_StrFree( vStore );
}
void Abc_NtkOrderFaninsByLitCount( Abc_Ntk_t * pNtk )
{
    Vec_Int_t * vOrder;
    Vec_Int_t * vCounts;
    Vec_Int_t * vFanins;
    Vec_Str_t * vStore;
    Abc_Obj_t * pNode;
    char * pSop, * pSopNew;
    char * pCube, * pCubeNew;
    int nVars, i, v, * pOrder;
    assert( Abc_NtkIsSopLogic(pNtk) );
    vOrder = Vec_IntAlloc( 100 );
    vStore = Vec_StrAlloc( 100 );
    vCounts = Vec_IntAlloc( 100 );
    vFanins = Vec_IntAlloc( 100 );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        pSop = (char *)pNode->pData;
        nVars = Abc_SopGetVarNum(pSop);
        assert( nVars == Abc_ObjFaninNum(pNode) );
        // count literals
        Vec_IntFill( vCounts, nVars, 0 );
        Abc_SopForEachCube( pSop, nVars, pCube )
            for ( v = 0; v < nVars; v++ )
                if ( pCube[v] != '-' )
                    Vec_IntAddToEntry( vCounts, v, 1 );
        // find good order
        Vec_IntClear( vOrder );
        for ( v = 0; v < nVars; v++ )
            Vec_IntPush( vOrder, v );
        pOrder = Vec_IntArray(vOrder);
        Vec_IntSelectSortCost( pOrder, nVars, vCounts );
        // copy the cover
        Vec_StrGrow( vStore, Abc_SopGetCubeNum(pSop) * (nVars + 3) + 1 );
        memcpy( Vec_StrArray(vStore), pSop, Abc_SopGetCubeNum(pSop) * (nVars + 3) + 1 );
        pSopNew = pCubeNew = pSop;
        pSop = Vec_StrArray(vStore);
        // generate permuted one
        Abc_SopForEachCube( pSop, nVars, pCube )
        {
            for ( v = 0; v < nVars; v++ )
                pCubeNew[v] = '-';
            for ( v = 0; v < nVars; v++ )
                if ( pCube[pOrder[v]] == '0' )
                    pCubeNew[v] = '0';
                else if ( pCube[pOrder[v]] == '1' )
                    pCubeNew[v] = '1';
            pCubeNew += nVars + 3;
        }
        pNode->pData = pSopNew;
        // generate the fanin order
        Vec_IntClear( vFanins );
        for ( v = 0; v < nVars; v++ )
            Vec_IntPush( vFanins, Abc_ObjFaninId( pNode, pOrder[v] ) );
        Vec_IntClear( &pNode->vFanins );
        Vec_IntAppend( &pNode->vFanins, vFanins );
    }
    Vec_IntFree( vFanins );
    Vec_IntFree( vCounts );
    Vec_IntFree( vOrder );
    Vec_StrFree( vStore );
}
void Abc_NtkOrderFaninsByLitCountAndCubeCount( Abc_Ntk_t * pNtk )
{
    // assuming that the fanins are sorted by the number of literals in each cube
    // this procedure sorts the literals appearing only once by the number of their cube
    Vec_Int_t * vOrder;
    Vec_Int_t * vCounts;
    Vec_Int_t * vFanins;
    Vec_Int_t * vCubeNum;
    Vec_Str_t * vStore;
    Abc_Obj_t * pNode;
    char * pSop, * pSopNew;
    char * pCube, * pCubeNew;
    int nVars, i, v, iCube, * pOrder;
    assert( Abc_NtkIsSopLogic(pNtk) );
    vStore = Vec_StrAlloc( 100 );
    vOrder = Vec_IntAlloc( 100 );
    vCounts = Vec_IntAlloc( 100 );
    vFanins = Vec_IntAlloc( 100 );
    vCubeNum = Vec_IntAlloc( 100 );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        pSop = (char *)pNode->pData;
        nVars = Abc_SopGetVarNum(pSop);
        assert( nVars == Abc_ObjFaninNum(pNode) );
        // count literals and remember the cube where each literal appears
        Vec_IntFill( vCounts, nVars, 0 );
        Vec_IntFill( vCubeNum, nVars, 0 );
        iCube = 0;
        Abc_SopForEachCube( pSop, nVars, pCube )
        {
            for ( v = 0; v < nVars; v++ )
                if ( pCube[v] != '-' )
                {
                    Vec_IntAddToEntry( vCounts, v, 1 );
                    Vec_IntWriteEntry( vCubeNum, v, iCube );
                }
            iCube++;
        }
        // create new order
        for ( v = 0; v < nVars; v++ )
            if ( Vec_IntEntry(vCounts, v) == 1 )
                Vec_IntWriteEntry( vCounts, v, Vec_IntEntry(vCubeNum, v) );
            else
                Vec_IntWriteEntry( vCounts, v, ABC_INFINITY );
        // find good order
        Vec_IntClear( vOrder );
        for ( v = 0; v < nVars; v++ )
            Vec_IntPush( vOrder, v );
        pOrder = Vec_IntArray(vOrder);
        Vec_IntSelectSortCost( pOrder, nVars, vCounts );
        // copy the cover
        Vec_StrGrow( vStore, Abc_SopGetCubeNum(pSop) * (nVars + 3) + 1 );
        memcpy( Vec_StrArray(vStore), pSop, Abc_SopGetCubeNum(pSop) * (nVars + 3) + 1 );
        pSopNew = pCubeNew = pSop;
        pSop = Vec_StrArray(vStore);
        // generate permuted one
        Abc_SopForEachCube( pSop, nVars, pCube )
        {
            for ( v = 0; v < nVars; v++ )
                pCubeNew[v] = '-';
            for ( v = 0; v < nVars; v++ )
                if ( pCube[pOrder[v]] == '0' )
                    pCubeNew[v] = '0';
                else if ( pCube[pOrder[v]] == '1' )
                    pCubeNew[v] = '1';
            pCubeNew += nVars + 3;
        }
        pNode->pData = pSopNew;
        // generate the fanin order
        Vec_IntClear( vFanins );
        for ( v = 0; v < nVars; v++ )
            Vec_IntPush( vFanins, Abc_ObjFaninId( pNode, pOrder[v] ) );
        Vec_IntClear( &pNode->vFanins );
        Vec_IntAppend( &pNode->vFanins, vFanins );
    }
    Vec_IntFree( vCubeNum );
    Vec_IntFree( vFanins );
    Vec_IntFree( vCounts );
    Vec_IntFree( vOrder );
    Vec_StrFree( vStore );
}

/**Function*************************************************************

  Synopsis    [Checks if the network is SCC-free.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Abc_CubeContain( char * pCube1, char * pCube2, int nVars )
{
    int v, fCont12 = 1, fCont21 = 1;
    for ( v = 0; v < nVars; v++ )
    {
        if ( pCube1[v] == pCube2[v] )
            continue;
        if ( pCube1[v] == '-' )
            fCont21 = 0;
        else if ( pCube2[v] == '-' )
            fCont12 = 0;
        else
            return 0;
        if ( !fCont21 && !fCont21 )
            return 0;
    }
    assert( fCont21 || fCont12 );
    return (fCont21 << 1) | fCont12;
}
int Abc_NodeMakeSCCFree( Abc_Obj_t * pNode, Vec_Ptr_t * vCubes )
{
    char * pSop = (char *)pNode->pData;
    char * pCube, * pCube2;
    int i, k, Status, nCount = 0;
    int nVars = Abc_ObjFaninNum(pNode);
    Vec_PtrClear( vCubes );
    Abc_SopForEachCube( pSop, nVars, pCube )
        Vec_PtrPush( vCubes, pCube );
    Vec_PtrForEachEntry( char *, vCubes, pCube, i )
    if ( pCube != NULL )
        Vec_PtrForEachEntryStart( char *, vCubes, pCube2, k, i+1 )
        if ( pCube2 != NULL )
        {
            Status = Abc_CubeContain( pCube, pCube2, nVars );
            nCount += (int)(Status > 0);
            if ( Status & 1 )
                Vec_PtrWriteEntry( vCubes, k, NULL );
            else if ( Status & 2 )
                Vec_PtrWriteEntry( vCubes, i, NULL );
        }
    if ( nCount == 0 )
        return 0;
    return 1;
}
void Abc_NtkMakeSCCFree( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vCubes;
    Abc_Obj_t * pNode;
    int i;
    assert( Abc_NtkIsSopLogic(pNtk) );
    vCubes = Vec_PtrAlloc( 1000 );
    Abc_NtkForEachNode( pNtk, pNode, i )
        if ( Abc_NodeMakeSCCFree( pNode, vCubes ) )
        {
            printf( "Node %d is not SCC-free.\n", i );
            break;
        }
    Vec_PtrFree( vCubes );
}

/**Function*************************************************************

  Synopsis    [Split large nodes by dividing their SOPs in half.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeSplitLarge( Abc_Obj_t * pNode )
{
    Abc_Obj_t * pNode1, * pNode2, * pFanin;
    int CutPoint, nVars = Abc_ObjFaninNum(pNode);
    int i, nCubes = Abc_SopGetCubeNum((char *)pNode->pData);
    pNode1 = Abc_NtkDupObj( pNode->pNtk, pNode, 0 );
    pNode2 = Abc_NtkDupObj( pNode->pNtk, pNode, 0 );
    Abc_ObjForEachFanin( pNode, pFanin, i )
        Abc_ObjAddFanin( pNode1, pFanin );
    Abc_ObjForEachFanin( pNode, pFanin, i )
        Abc_ObjAddFanin( pNode2, pFanin );    
    // update the node
    Abc_ObjRemoveFanins( pNode );
    Abc_ObjAddFanin( pNode, pNode1 );
    Abc_ObjAddFanin( pNode, pNode2 );
    pNode->pData = Abc_SopCreateOr( (Mem_Flex_t *)pNode->pNtk->pManFunc, 2, NULL );
    // update covers of the nodes
    assert( nCubes > 1 );
    CutPoint = (nCubes / 2) * (nVars + 3);
    ((char *)pNode1->pData)[CutPoint] = 0;
    pNode2->pData = (char *)pNode2->pData + CutPoint;
}
void Abc_NtkSplitLarge( Abc_Ntk_t * pNtk, int nFaninsMax, int nCubesMax )
{
    Abc_Obj_t * pNode;
    int nObjOld = Abc_NtkObjNumMax(pNtk);
    int i, nCubes;
    assert( Abc_NtkIsSopLogic(pNtk) );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        if ( i == nObjOld )
            break;
        nCubes = Abc_SopGetCubeNum((char *)pNode->pData);
        if ( (Abc_ObjFaninNum(pNode) > nFaninsMax && nCubes > 1) || nCubes > nCubesMax )
            Abc_NodeSplitLarge( pNode );
    }
}

/**Function*************************************************************

  Synopsis    [Sorts the cubes in a topological order.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NodeCompareCubes( char ** pp1, char ** pp2 )
{
    return strcmp( *pp1, *pp2 );
}
void Abc_NodeSortCubes( Abc_Obj_t * pNode, Vec_Ptr_t * vCubes, Vec_Str_t * vStore )
{
    char * pCube, * pPivot;
    char * pSop = (char *)pNode->pData;
    int i, nVars = Abc_ObjFaninNum(pNode);
    Vec_PtrClear( vCubes );
    Abc_SopForEachCube( pSop, nVars, pCube )
    {
        assert( pCube[nVars] == ' ' );
        pCube[nVars] = 0;
        Vec_PtrPush( vCubes, pCube );
    }
    Vec_PtrSort( vCubes, (int (*)())Abc_NodeCompareCubes );
    Vec_StrGrow( vStore, Vec_PtrSize(vCubes) * (nVars + 3) );
    pPivot = Vec_StrArray( vStore );
    Vec_PtrForEachEntry( char *, vCubes, pCube, i )
    {
        assert( pCube[nVars] == 0 );
        pCube[nVars] = ' ';
        memcpy( pPivot, pCube, nVars + 3 );
        pPivot += nVars + 3;
    }
    memcpy( pSop, Vec_StrArray(vStore), Vec_PtrSize(vCubes) * (nVars + 3) );
}
void Abc_NtkSortCubes( Abc_Ntk_t * pNtk )
{
    Vec_Ptr_t * vCubes;
    Vec_Str_t * vStore;
    Abc_Obj_t * pNode;
    int i;
    assert( Abc_NtkIsSopLogic(pNtk) );
    vCubes = Vec_PtrAlloc( 1000 );
    vStore = Vec_StrAlloc( 1000 );
    Abc_NtkForEachNode( pNtk, pNode, i )
        Abc_NodeSortCubes( pNode, vCubes, vStore );
    Vec_StrFree( vStore );
    Vec_PtrFree( vCubes );
}

/**Function*************************************************************

  Synopsis    [Sorts fanins of each node to make SOPs more readable.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkSortSops( Abc_Ntk_t * pNtk )
{
    Abc_NtkOrderFaninsByLitCount( pNtk );
    Abc_NtkSortCubes( pNtk );
    Abc_NtkOrderFaninsByLitCountAndCubeCount( pNtk );
    Abc_NtkSortCubes( pNtk );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

