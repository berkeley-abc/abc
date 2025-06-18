/**CFile****************************************************************

  FileName    [abcLutmin.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Minimization of the number of LUTs.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcLutmin.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"

#ifdef ABC_USE_CUDD
#include "bdd/extrab/extraBdd.h"
#endif

ABC_NAMESPACE_IMPL_START


/* 
    Implememented here is the algorithm for minimal-LUT decomposition
    described in the paper: T. Sasao et al. "On the number of LUTs 
    to implement logic functions", To appear in Proc. IWLS'09.
*/

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

#ifdef ABC_USE_CUDD

/**Function*************************************************************

  Synopsis    [Check if a LUT can absort a fanin.]

  Description [The fanins are (c, d0, d1).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ObjCheckAbsorb( Abc_Obj_t * pObj, Abc_Obj_t * pPivot, int nLutSize, Vec_Ptr_t * vFanins )
{
    Abc_Obj_t * pFanin;
    int i;
    assert( Abc_ObjIsNode(pObj) && Abc_ObjIsNode(pPivot) );
    // add fanins of the node
    Vec_PtrClear( vFanins );
    Abc_ObjForEachFanin( pObj, pFanin, i )
        if ( pFanin != pPivot )
            Vec_PtrPush( vFanins, pFanin );
    // add fanins of the fanin
    Abc_ObjForEachFanin( pPivot, pFanin, i )
    {
        Vec_PtrPushUnique( vFanins, pFanin );
        if ( Vec_PtrSize(vFanins) > nLutSize )
            return 0;
    }
    return 1;
} 

/**Function*************************************************************

  Synopsis    [Check how many times a LUT can absorb a fanin.]

  Description [The fanins are (c, d0, d1).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkCheckAbsorb( Abc_Ntk_t * pNtk, int nLutSize )
{
    Vec_Int_t * vCounts;
    Vec_Ptr_t * vFanins;
    Abc_Obj_t * pObj, * pFanin;
    int i, k, Counter = 0, Counter2 = 0;
    abctime clk = Abc_Clock();
    vCounts = Vec_IntStart( Abc_NtkObjNumMax(pNtk) );
    vFanins = Vec_PtrAlloc( 100 );
    Abc_NtkForEachNode( pNtk, pObj, i )
    Abc_ObjForEachFanin( pObj, pFanin, k )
        if ( Abc_ObjIsNode(pFanin) && Abc_ObjCheckAbsorb( pObj, pFanin, nLutSize, vFanins ) )
        {
            Vec_IntAddToEntry( vCounts, Abc_ObjId(pFanin), 1 );
            Counter++;
        }
    Vec_PtrFree( vFanins );
    Abc_NtkForEachNode( pNtk, pObj, i )
        if ( Vec_IntEntry(vCounts, Abc_ObjId(pObj)) == Abc_ObjFanoutNum(pObj) )
        {
//            printf( "%d ", Abc_ObjId(pObj) );
            Counter2++;
        }
    printf( "Absorted = %6d. (%6.2f %%)   Fully = %6d. (%6.2f %%)  ", 
        Counter,  100.0 * Counter  / Abc_NtkNodeNum(pNtk), 
        Counter2, 100.0 * Counter2 / Abc_NtkNodeNum(pNtk) );
    Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    Vec_IntFree( vCounts );
}

/**Function*************************************************************

  Synopsis    [Implements 2:1 MUX using one 3-LUT.]

  Description [The fanins are (c, d0, d1).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkBddMux21( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pFanins[] )
{
    DdManager * dd = (DdManager *)pNtkNew->pManFunc;
    Abc_Obj_t * pNode;
    DdNode * bSpin, * bCof0, * bCof1;
    pNode = Abc_NtkCreateNode( pNtkNew );
    Abc_ObjAddFanin( pNode, pFanins[0] );
    Abc_ObjAddFanin( pNode, pFanins[1] );
    Abc_ObjAddFanin( pNode, pFanins[2] );
    bSpin = Cudd_bddIthVar(dd, 0);
    bCof0 = Cudd_bddIthVar(dd, 1); 
    bCof1 = Cudd_bddIthVar(dd, 2); 
    pNode->pData = Cudd_bddIte( dd, bSpin, bCof1, bCof0 );  Cudd_Ref( (DdNode *)pNode->pData ); 
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Implements 4:1 MUX using one 6-LUT.]

  Description [The fanins are (c0, c1, d00, d01, d10, d11).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkBddMux411( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pFanins[] )
{
    DdManager * dd = (DdManager *)pNtkNew->pManFunc;
    Abc_Obj_t * pNode;
    DdNode * bSpin, * bCof0, * bCof1;
    pNode = Abc_NtkCreateNode( pNtkNew );
    Abc_ObjAddFanin( pNode, pFanins[0] );
    Abc_ObjAddFanin( pNode, pFanins[1] );
    Abc_ObjAddFanin( pNode, pFanins[2] );
    Abc_ObjAddFanin( pNode, pFanins[3] );
    Abc_ObjAddFanin( pNode, pFanins[4] );
    Abc_ObjAddFanin( pNode, pFanins[5] );
    bSpin = Cudd_bddIthVar(dd, 1);
    bCof0 = Cudd_bddIte( dd, bSpin, Cudd_bddIthVar(dd, 3), Cudd_bddIthVar(dd, 2) ); Cudd_Ref( bCof0 );
    bCof1 = Cudd_bddIte( dd, bSpin, Cudd_bddIthVar(dd, 5), Cudd_bddIthVar(dd, 4) ); Cudd_Ref( bCof1 );
    bSpin = Cudd_bddIthVar(dd, 0);
    pNode->pData = Cudd_bddIte( dd, bSpin, bCof1, bCof0 );  Cudd_Ref( (DdNode *)pNode->pData ); 
    Cudd_RecursiveDeref( dd, bCof0 );
    Cudd_RecursiveDeref( dd, bCof1 );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Implementes 4:1 MUX using two 4-LUTs.]

  Description [The fanins are (c0, c1, d00, d01, d10, d11).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkBddMux412( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pFanins[] )
{
    DdManager * dd = (DdManager *)pNtkNew->pManFunc;
    Abc_Obj_t * pNodeBot, * pNodeTop;
    DdNode * bSpin, * bCof0, * bCof1;
    // bottom node
    pNodeBot = Abc_NtkCreateNode( pNtkNew );
    Abc_ObjAddFanin( pNodeBot, pFanins[0] );
    Abc_ObjAddFanin( pNodeBot, pFanins[1] );
    Abc_ObjAddFanin( pNodeBot, pFanins[2] );
    Abc_ObjAddFanin( pNodeBot, pFanins[3] );
    bSpin = Cudd_bddIthVar(dd, 0);
    bCof0 = Cudd_bddIte( dd, Cudd_bddIthVar(dd, 1), Cudd_bddIthVar(dd, 3), Cudd_bddIthVar(dd, 2) ); Cudd_Ref( bCof0 );
    bCof1 = Cudd_bddIthVar(dd, 1);
    pNodeBot->pData = Cudd_bddIte( dd, bSpin, bCof1, bCof0 );  Cudd_Ref( (DdNode *)pNodeBot->pData ); 
    Cudd_RecursiveDeref( dd, bCof0 );
    // top node
    pNodeTop = Abc_NtkCreateNode( pNtkNew );
    Abc_ObjAddFanin( pNodeTop, pFanins[0] );
    Abc_ObjAddFanin( pNodeTop, pNodeBot   );
    Abc_ObjAddFanin( pNodeTop, pFanins[4] );
    Abc_ObjAddFanin( pNodeTop, pFanins[5] );
    bSpin = Cudd_bddIthVar(dd, 0);
    bCof0 = Cudd_bddIthVar(dd, 1);
    bCof1 = Cudd_bddIte( dd, Cudd_bddIthVar(dd, 1), Cudd_bddIthVar(dd, 3), Cudd_bddIthVar(dd, 2) ); Cudd_Ref( bCof1 );
    pNodeTop->pData = Cudd_bddIte( dd, bSpin, bCof1, bCof0 );  Cudd_Ref( (DdNode *)pNodeTop->pData ); 
    Cudd_RecursiveDeref( dd, bCof1 );
    return pNodeTop;
}

/**Function*************************************************************

  Synopsis    [Implementes 4:1 MUX using two 4-LUTs.]

  Description [The fanins are (c0, c1, d00, d01, d10, d11).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkBddMux412a( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pFanins[] )
{
    DdManager * dd = (DdManager *)pNtkNew->pManFunc;
    Abc_Obj_t * pNodeBot, * pNodeTop;
    DdNode * bSpin, * bCof0, * bCof1;
    // bottom node
    pNodeBot = Abc_NtkCreateNode( pNtkNew );
    Abc_ObjAddFanin( pNodeBot, pFanins[1] );
    Abc_ObjAddFanin( pNodeBot, pFanins[2] );
    Abc_ObjAddFanin( pNodeBot, pFanins[3] );
    bSpin = Cudd_bddIthVar(dd, 0);
    bCof0 = Cudd_bddIthVar(dd, 1);
    bCof1 = Cudd_bddIthVar(dd, 2);
    pNodeBot->pData = Cudd_bddIte( dd, bSpin, bCof1, bCof0 );  Cudd_Ref( (DdNode *)pNodeBot->pData ); 
    // top node
    pNodeTop = Abc_NtkCreateNode( pNtkNew );
    Abc_ObjAddFanin( pNodeTop, pFanins[0] );
    Abc_ObjAddFanin( pNodeTop, pFanins[1] );
    Abc_ObjAddFanin( pNodeTop, pNodeBot   );
    Abc_ObjAddFanin( pNodeTop, pFanins[4] );
    Abc_ObjAddFanin( pNodeTop, pFanins[5] );
    bSpin = Cudd_bddIthVar(dd, 0);
    bCof0 = Cudd_bddIthVar(dd, 2);
    bCof1 = Cudd_bddIte( dd, Cudd_bddIthVar(dd, 1), Cudd_bddIthVar(dd, 4), Cudd_bddIthVar(dd, 3) ); Cudd_Ref( bCof1 );
    pNodeTop->pData = Cudd_bddIte( dd, bSpin, bCof1, bCof0 );  Cudd_Ref( (DdNode *)pNodeTop->pData ); 
    Cudd_RecursiveDeref( dd, bCof1 );
    return pNodeTop;
}

/**Function*************************************************************

  Synopsis    [Implements 4:1 MUX using three 2:1 MUXes.]

  Description [The fanins are (c0, c1, d00, d01, d10, d11).]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkBddMux413( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pFanins[] )
{
    Abc_Obj_t * pNodesBot[3], * pNodesTop[3];
    // left bottom
    pNodesBot[0] = pFanins[1];
    pNodesBot[1] = pFanins[2];
    pNodesBot[2] = pFanins[3];
    pNodesTop[1] = Abc_NtkBddMux21( pNtkNew, pNodesBot );
    // right bottom
    pNodesBot[0] = pFanins[1];
    pNodesBot[1] = pFanins[4];
    pNodesBot[2] = pFanins[5];
    pNodesTop[2] = Abc_NtkBddMux21( pNtkNew, pNodesBot );
    // top node
    pNodesTop[0] = pFanins[0];
    return Abc_NtkBddMux21( pNtkNew, pNodesTop );
}

/**Function*************************************************************

  Synopsis    [Finds unique cofactors of the function on the given level.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Abc_NtkBddCofactors_rec( DdManager * dd, DdNode * bNode, int iCof, int iLevel, int nLevels )
{
    DdNode * bNode0, * bNode1;
    if ( Cudd_IsConstant(bNode) || iLevel == nLevels )
        return bNode;
    if ( Cudd_ReadPerm( dd, Cudd_NodeReadIndex(bNode) ) > iLevel )
    {
        bNode0 = bNode;
        bNode1 = bNode;
    }
    else if ( Cudd_IsComplement(bNode) )
    {
        bNode0 = Cudd_Not(cuddE(Cudd_Regular(bNode)));
        bNode1 = Cudd_Not(cuddT(Cudd_Regular(bNode)));
    }
    else
    {
        bNode0 = cuddE(bNode);
        bNode1 = cuddT(bNode);
    }
    if ( (iCof >> (nLevels-1-iLevel)) & 1 )
        return Abc_NtkBddCofactors_rec( dd, bNode1, iCof, iLevel + 1, nLevels );
    return Abc_NtkBddCofactors_rec( dd, bNode0, iCof, iLevel + 1, nLevels );
}

/**Function*************************************************************

  Synopsis    [Finds unique cofactors of the function on the given level.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Ptr_t * Abc_NtkBddCofactors( DdManager * dd, DdNode * bNode, int Level )
{
    Vec_Ptr_t * vCofs;
    int i, nCofs = (1<<Level);
    assert( Level > 0 && Level < 10 );
    vCofs = Vec_PtrAlloc( 8 );
    for ( i = 0; i < nCofs; i++ )
        Vec_PtrPush( vCofs, Abc_NtkBddCofactors_rec( dd, bNode, i, 0, Level ) );
    return vCofs;
}

/**Function*************************************************************

  Synopsis    [Comparison procedure for two integers.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static int Vec_PtrSortCompare( void ** pp1, void ** pp2 )
{
    if ( *pp1 < *pp2 )
        return -1;
    if ( *pp1 > *pp2 )
        return 1;
    return 0;
}

/**Function*************************************************************

  Synopsis    [Converts the node to MUXes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkCreateCofLut( Abc_Ntk_t * pNtkNew, DdManager * dd, DdNode * bCof, Abc_Obj_t * pNode, int Level )
{
    int fVerbose = 0;
    DdNode * bFuncNew;
    Abc_Obj_t * pNodeNew;
    int i;
    assert( Abc_ObjFaninNum(pNode) > Level );
    // create a new node
    pNodeNew = Abc_NtkCreateNode( pNtkNew );
    // add the fanins in the order, in which they appear in the reordered manager
    for ( i = Level; i < Abc_ObjFaninNum(pNode); i++ )
        Abc_ObjAddFanin( pNodeNew, Abc_ObjFanin(pNode, i)->pCopy );
if ( fVerbose )
{
Extra_bddPrint( dd, bCof );
printf( "\n" );
printf( "\n" );
}
    // transfer the function
    bFuncNew = Extra_bddMove( dd, bCof, -Level );  Cudd_Ref( bFuncNew );
if ( fVerbose )
{
Extra_bddPrint( dd, bFuncNew );
printf( "\n" );
printf( "\n" );
}
    pNodeNew->pData = Extra_TransferLevelByLevel( dd, (DdManager *)pNtkNew->pManFunc, bFuncNew );  Cudd_Ref( (DdNode *)pNodeNew->pData );
//Extra_bddPrint( pNtkNew->pManFunc, pNodeNew->pData );
//printf( "\n" );
//printf( "\n" );
    Cudd_RecursiveDeref( dd, bFuncNew );
    return pNodeNew;
}

/**Function*************************************************************

  Synopsis    [Performs one step of Ashenhurst-Curtis decomposition.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkBddCurtis( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pNode, Vec_Ptr_t * vCofs, Vec_Ptr_t * vUniq )
{
    DdManager * ddOld = (DdManager *)pNode->pNtk->pManFunc;
    DdManager * ddNew = (DdManager *)pNtkNew->pManFunc;
    DdNode * bCof, * bUniq, * bMint, * bTemp, * bFunc, * bBits[10], ** pbCodeVars;
    Abc_Obj_t * pNodeNew = NULL, * pNodeBS[10];
    int nLutSize = Abc_Base2Log( Vec_PtrSize(vCofs) );
    int nBits    = Abc_Base2Log( Vec_PtrSize(vUniq) );
    int b, c, u, i;
    assert( nBits + 2 <= nLutSize );
    assert( nLutSize < Abc_ObjFaninNum(pNode) );
    // start BDDs for the decomposed blocks
    for ( b = 0; b < nBits; b++ )
        bBits[b] = Cudd_ReadLogicZero(ddNew), Cudd_Ref( bBits[b] );
    // add each bound set minterm to one of the blocks
    Vec_PtrForEachEntry( DdNode *, vCofs, bCof, c )
    {
        Vec_PtrForEachEntry( DdNode *, vUniq, bUniq, u )
            if ( bUniq == bCof )
                break;
        assert( u < Vec_PtrSize(vUniq) );
        for ( b = 0; b < nBits; b++ )
        {
            if ( ((u >> b) & 1) == 0 )
                continue;
            bMint = Extra_bddBitsToCube( ddNew, c, nLutSize, ddNew->vars, 1 );  Cudd_Ref( bMint );
            bBits[b] = Cudd_bddOr( ddNew, bTemp = bBits[b], bMint );  Cudd_Ref( bBits[b] );
            Cudd_RecursiveDeref( ddNew, bTemp );
            Cudd_RecursiveDeref( ddNew, bMint );
        }
    }
    // create bound set nodes
    for ( b = 0; b < nBits; b++ )
    {
        pNodeBS[b] = Abc_NtkCreateNode( pNtkNew );
        for ( i = 0; i < nLutSize; i++ )
            Abc_ObjAddFanin( pNodeBS[b], Abc_ObjFanin(pNode, i)->pCopy );
        pNodeBS[b]->pData = bBits[b]; // takes ref
    }
    // create composition node
    pNodeNew = Abc_NtkCreateNode( pNtkNew );
    // add free set variables first
    for ( i = nLutSize; i < Abc_ObjFaninNum(pNode); i++ )
        Abc_ObjAddFanin( pNodeNew, Abc_ObjFanin(pNode, i)->pCopy );
    // add code bit variables next
    for ( b = 0; b < nBits; b++ )
        Abc_ObjAddFanin( pNodeNew, pNodeBS[b] );
    // derive function of the composition node
    bFunc = Cudd_ReadLogicZero(ddNew); Cudd_Ref( bFunc );
    pbCodeVars = ddNew->vars + Abc_ObjFaninNum(pNode) - nLutSize;
    Vec_PtrForEachEntry( DdNode *, vUniq, bUniq, u )
    {
        bUniq = Extra_bddMove( ddOld, bUniq, -nLutSize );                   Cudd_Ref( bUniq );
        bUniq = Extra_TransferLevelByLevel( ddOld, ddNew, bTemp = bUniq );  Cudd_Ref( bUniq );
        Cudd_RecursiveDeref( ddOld, bTemp );

        bMint = Extra_bddBitsToCube( ddNew, u, nBits, pbCodeVars, 0 );  Cudd_Ref( bMint );
        bMint = Cudd_bddAnd( ddNew, bTemp = bMint, bUniq );  Cudd_Ref( bMint );
        Cudd_RecursiveDeref( ddNew, bTemp );
        Cudd_RecursiveDeref( ddNew, bUniq );

        bFunc = Cudd_bddOr( ddNew, bTemp = bFunc, bMint );  Cudd_Ref( bFunc );
        Cudd_RecursiveDeref( ddNew, bTemp );
        Cudd_RecursiveDeref( ddNew, bMint );
    }
    pNodeNew->pData = bFunc; // takes ref
    return pNodeNew;
}

/**Function*************************************************************

  Synopsis    [Tries to decompose using cofactoring into two LUTs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkBddFindCofactor( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pNode, int nLutSize )
{
    Abc_Obj_t * pNodeBot, * pNodeTop;
    DdManager * ddOld = (DdManager *)pNode->pNtk->pManFunc;
    DdManager * ddNew = (DdManager *)pNtkNew->pManFunc;
    DdNode * bCof0 = NULL, * bCof1 = NULL, * bSupp, * bTemp, * bVar;
    DdNode * bCof0n, * bCof1n;
    int i, iCof, iFreeVar, fCof1Smaller = -1;
    assert( Abc_ObjFaninNum(pNode) == nLutSize + 1 );
    for ( iCof = 0; iCof < Abc_ObjFaninNum(pNode); iCof++ )
    {
        bVar  = Cudd_bddIthVar( ddOld, iCof );
        bCof0 = Cudd_Cofactor( ddOld, (DdNode *)pNode->pData, Cudd_Not(bVar) );  Cudd_Ref( bCof0 );
        bCof1 = Cudd_Cofactor( ddOld, (DdNode *)pNode->pData, bVar  );           Cudd_Ref( bCof1 );
        if ( Cudd_SupportSize( ddOld, bCof0 ) <= nLutSize - 2 )
        {
            fCof1Smaller = 0;
            break;
        }
        if ( Cudd_SupportSize( ddOld, bCof1 ) <= nLutSize - 2 )
        {
            fCof1Smaller = 1;
            break;
        }
        Cudd_RecursiveDeref( ddOld, bCof0 );
        Cudd_RecursiveDeref( ddOld, bCof1 );
    }
    if ( iCof == Abc_ObjFaninNum(pNode) )
        return NULL;
    // find unused variable
    bSupp = Cudd_Support( ddOld, fCof1Smaller? bCof1 : bCof0 );   Cudd_Ref( bSupp );
    iFreeVar = -1;
    for ( i = 0; i < Abc_ObjFaninNum(pNode); i++ )
    {
        assert( i == Cudd_ReadPerm(ddOld, i) );
        if ( i == iCof )
            continue;
        for ( bTemp = bSupp; !Cudd_IsConstant(bTemp); bTemp = cuddT(bTemp) )
            if ( i == (int)Cudd_NodeReadIndex(bTemp) )
                break;
        if ( Cudd_IsConstant(bTemp) )
        {
            iFreeVar = i;
            break;
        }
    }
    assert( iFreeVar != iCof && iFreeVar < Abc_ObjFaninNum(pNode) );
    Cudd_RecursiveDeref( ddOld, bSupp );
    // transfer the cofactors
    bCof0n = Extra_TransferLevelByLevel( ddOld, ddNew, bCof0 ); Cudd_Ref( bCof0n );
    bCof1n = Extra_TransferLevelByLevel( ddOld, ddNew, bCof1 ); Cudd_Ref( bCof1n );
    Cudd_RecursiveDeref( ddOld, bCof0 );
    Cudd_RecursiveDeref( ddOld, bCof1 );
    // create bottom node
    pNodeBot = Abc_NtkCreateNode( pNtkNew );
    for ( i = 0; i < Abc_ObjFaninNum(pNode); i++ )
        Abc_ObjAddFanin( pNodeBot, Abc_ObjFanin(pNode, i)->pCopy );
    pNodeBot->pData = fCof1Smaller? bCof0n : bCof1n;
    // create top node
    pNodeTop = Abc_NtkCreateNode( pNtkNew );
    for ( i = 0; i < Abc_ObjFaninNum(pNode); i++ )
        if ( i == iFreeVar )           
            Abc_ObjAddFanin( pNodeTop, pNodeBot );
        else
            Abc_ObjAddFanin( pNodeTop, Abc_ObjFanin(pNode, i)->pCopy );
    // derive the new function
    pNodeTop->pData = Cudd_bddIte( ddNew, 
        Cudd_bddIthVar(ddNew, iCof), 
        fCof1Smaller? bCof1n : Cudd_bddIthVar(ddNew, iFreeVar), 
        fCof1Smaller? Cudd_bddIthVar(ddNew, iFreeVar) : bCof0n );
    Cudd_Ref( (DdNode *)pNodeTop->pData );
    Cudd_RecursiveDeref( ddNew, fCof1Smaller? bCof1n : bCof0n );
    return pNodeTop;
}


/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkBddNodeCompareByLevel( DdNode ** pp1, DdNode ** pp2 )
{
    return (*pp1)->Id - (*pp2)->Id;
}
Vec_Ptr_t * Abc_NtkBddCollectByLevel( DdManager * dd, DdNode * aFunc )
{
    DdGen *gen; DdNode *node; int i;
    Vec_Ptr_t * vNodes = Vec_PtrAlloc( 100 );
    Cudd_ForeachNode( dd, aFunc, gen, node ) 
        Vec_PtrPush( vNodes, node ), node->Id = Cudd_ReadPerm( dd, (int)node->index );
    Vec_PtrSort( vNodes, (int (*)(const void *, const void *))Abc_NtkBddNodeCompareByLevel );
    Vec_PtrForEachEntry( DdNode *, vNodes, node, i )
        node->Id = i;
    return vNodes;
}
void Abc_NtkBddCollectPrint3( DdManager * dd, DdNode * aFunc )
{
    Vec_Ptr_t * vNodes = Abc_NtkBddCollectByLevel( dd, aFunc );
    Vec_PtrPrintPointers( vNodes );
    Vec_PtrFree( vNodes );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

Vec_Ptr_t * Abc_NtkBddFetchNodes( DdManager * dd, DdNode * aFunc )
{
    Vec_Ptr_t * vNodes = Vec_PtrAlloc( 100 );
    DdGen *gen; DdNode *node;
    Cudd_ForeachNode( dd, aFunc, gen, node) 
        Vec_PtrPush(vNodes, node), node->Id = 0;
    return vNodes;
}
void Abc_NtkBddCleanNodes( DdManager * dd, DdNode * aFunc )
{
    DdGen *gen; DdNode *node;
    Cudd_ForeachNode( dd, aFunc, gen, node) 
        node->Id = 0;
}
void Abc_NtkBddCollectPtr_rec( DdManager * dd, DdNode * aFunc, Vec_Ptr_t * vNodes )
{
    if ( aFunc->Id )
        return;
    if ( !cuddIsConstant(aFunc) ) {
        Abc_NtkBddCollectPtr_rec( dd, cuddE(aFunc), vNodes );
        Abc_NtkBddCollectPtr_rec( dd, cuddT(aFunc), vNodes );
    }
    aFunc->Id = Vec_PtrSize(vNodes) + 1;
    Vec_PtrPush(vNodes, aFunc);
}
Vec_Ptr_t * Abc_NtkBddCollectPtr( DdManager * dd, DdNode * aFunc )
{
    Vec_Ptr_t * vNodes = Vec_PtrAlloc( 100 );
    Abc_NtkBddCleanNodes( dd, aFunc );
    Abc_NtkBddCollectPtr_rec( dd, aFunc, vNodes );
    return vNodes;
}
void Abc_NtkBddCollectPrint2( DdManager * dd, DdNode * aFunc )
{
    Vec_Ptr_t * vNodes = Abc_NtkBddCollectPtr( dd, aFunc );
    Vec_PtrPrintPointers( vNodes );
    Vec_PtrFree( vNodes );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

static inline word     Abc_Bdd2Word( DdNode * f )              { union { DdNode * f; word w; } v; v.f = f; return v.w;     }
static inline DdNode * Abc_Word2Bdd( word w )                  { union { DdNode * f; word w; } v; v.w = w; return v.f;     }

static inline int      Abc_Bdd2Int( DdNode * F, DdNode * f )   { return (int)(Abc_Bdd2Word(F) ^ Abc_Bdd2Word(f)) >> 3;     }
static inline DdNode * Abc_Int2Bdd( DdNode * F, int diff )     { return Abc_Word2Bdd(Abc_Bdd2Word(F) ^ (word)(diff << 3)); }

static inline int  Abc_BddIndex( DdManager * dd, DdNode * f )  { return cuddIsConstant(f) ? dd->size : (int)f->index;      }
static inline int  Abc_BddLevel( DdManager * dd, DdNode * f )  { return cuddIsConstant(f) ? dd->size : Cudd_ReadPerm(dd, (int)f->index);  }

void Abc_NtkBddCollectInt_rec( DdManager * dd, DdNode * aRef, DdNode * aFunc, Vec_Wec_t * vNodes )
{
    if ( Cudd_IsComplement(aFunc->next) )
        return;
    aFunc->next = Cudd_Not(aFunc->next);
    if ( !cuddIsConstant(aFunc) ) {
        Abc_NtkBddCollectInt_rec( dd, aRef, cuddE(aFunc), vNodes );
        Abc_NtkBddCollectInt_rec( dd, aRef, cuddT(aFunc), vNodes );
    }
    //assert( Abc_Bdd2Int(aRef, aFunc) % 8 == 0 );
    Vec_WecPush( vNodes, Abc_BddLevel(dd, aFunc), Abc_Bdd2Int(aRef, aFunc) );        
}
Vec_Wec_t * Abc_NtkBddCollectInt( DdManager * dd, DdNode * aFunc )
{
    Vec_Wec_t * vNodes = Vec_WecStart( dd->size+1 );
    Abc_NtkBddCollectInt_rec( dd, aFunc, aFunc, vNodes );
    extern void ddClearFlag2( DdNode * f );
    ddClearFlag2( aFunc );
    return vNodes;
}
void Abc_NtkBddCollectPrint( DdManager * dd, DdNode * aFunc )
{
    Vec_Wec_t * vNodes = Abc_NtkBddCollectInt( dd, aFunc );
    Vec_WecPrint( vNodes, 0 );
    Vec_WecFree( vNodes );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Abc_NtkBddCollectHighest( DdManager * dd, DdNode * aFunc, Vec_Wec_t * vNodes )
{
    Vec_Int_t * vRes = Vec_IntStartFull( Vec_WecMaxEntry(vNodes)+1 );
    Vec_Int_t * vLevel; int i, k, Obj, * pEntry;
    Vec_WecForEachLevelStop( vNodes, vLevel, i, dd->size )
        Vec_IntForEachEntry( vLevel, Obj, k ) {
            DdNode * aNode = Abc_Int2Bdd(aFunc, Obj);            
            pEntry = Vec_IntEntryP( vRes, Abc_Bdd2Int(aFunc, cuddE(aNode)) );
            if ( *pEntry == -1 ) *pEntry = i;
            pEntry = Vec_IntEntryP( vRes, Abc_Bdd2Int(aFunc, cuddT(aNode)) );
            if ( *pEntry == -1 ) *pEntry = i;
        }
    return vRes;
}
void Abc_NtkBddCollectProfile( DdManager * dd, DdNode * aFunc, Vec_Wec_t * vNodes, int * pProf )
{
    memset( pProf, 0, sizeof(int)*(dd->size+1) );
    Vec_Int_t * vHighest = Abc_NtkBddCollectHighest( dd, aFunc, vNodes );
    Vec_Int_t * vLevel; int i, k, Obj;
    pProf[0] = 1;
    Vec_WecForEachLevelStart( vNodes, vLevel, i, 1 )
        Vec_IntForEachEntry( vLevel, Obj, k ) {
            int lev, Start = Vec_IntEntry( vHighest, Obj );
            for ( lev = Start+1; lev <= i; lev++ )
                pProf[lev]++;
        }
    printf( "  Size = %5d  ", Vec_IntSize(vHighest) );
    Vec_IntFree( vHighest );
}
void Abc_NtkBddTestProfile( DdManager * dd, DdNode * aFunc )
{
    Vec_Wec_t * vNodes = Abc_NtkBddCollectInt( dd, aFunc );
    int i, Total = 0, Profile[100]; assert( dd->size < 100 );
    Abc_NtkBddCollectProfile( dd, aFunc, vNodes, Profile );
    printf( "   " );
    for ( i = 0; i <= dd->size; i++ )
        printf( "%3d", Profile[i] ), Total += Profile[i];
    printf( "  Total = %d\n", Total );
    Vec_WecFree( vNodes );
}
Vec_Wec_t * Abc_NtkBddCollectCofs( DdManager * dd, DdNode * aFunc, Vec_Wec_t * vNodes )
{
    Vec_Wec_t * vCofs = Vec_WecStart( dd->size+1 );
    Vec_Int_t * vHighest = Abc_NtkBddCollectHighest( dd, aFunc, vNodes );
    Vec_Int_t * vLevel; int i, k, Obj;
    Vec_WecPush( vCofs, 0, 0 );
    Vec_WecForEachLevelStart( vNodes, vLevel, i, 1 )
        Vec_IntForEachEntry( vLevel, Obj, k ) {
            int lev, Start = Vec_IntEntry( vHighest, Obj );
            for ( lev = Start+1; lev <= i; lev++ )
                Vec_WecPush( vCofs, lev, Obj );
        }
    Vec_IntFree( vHighest );
    return vCofs;
}
Vec_Wec_t * Abc_NtkBddCollecInfo1( DdManager * dd, DdNode * aFunc )
{
    Vec_Wec_t * vInfo  = Vec_WecStart( dd->size );
    Vec_Wec_t * vNodes = Abc_NtkBddCollectInt( dd, aFunc );
    Vec_Wec_t * vCofs  = Abc_NtkBddCollectCofs( dd, aFunc, vNodes );
    Vec_Int_t * vLevel; int i, k, Obj;
    for ( int a = 0; a < dd->size; a++ ) {
        word Sign = (word)1 << a;
        for ( int n = 0; n < 2; n++ ) {
            word Value = (word)n << a;
            Vec_WecForEachLevel( vNodes, vLevel, i )
                Vec_IntForEachEntry( vLevel, Obj, k )
                    Abc_Int2Bdd(aFunc, Obj)->Id = 0;
            aFunc->Id = 1;
            //printf( " %c %d : ", 'a'+a, n );
            //printf( " %2d", 1 );
            if ( n == 0 )
                Vec_IntPush( Vec_WecEntry(vInfo, a), 1 );
            Vec_WecForEachLevelStop( vNodes, vLevel, i, dd->size ) {
                Vec_IntForEachEntry( vLevel, Obj, k ) {  
                    DdNode * aNode = Abc_Int2Bdd(aFunc, Obj);
                    if ( aNode->Id == 0 )
                        continue;
                    if ( !((Sign >> i) & 1) || ((Value >> i) & 1) == 0 )
                        cuddE(aNode)->Id |= 1;
                    if ( !((Sign >> i) & 1) || ((Value >> i) & 1) == 1 )
                        cuddT(aNode)->Id |= 1;
                }
                Vec_Int_t * vCof = Vec_WecEntry(vCofs, i+1);
                int Counter = 0;
                Vec_IntForEachEntry( vCof, Obj, k )
                    Counter += (int)Abc_Int2Bdd(aFunc, Obj)->Id;                
                if ( n == 0 )
                    Vec_IntPush( Vec_WecEntry(vInfo, a), Counter );
                else {
                    int * pEntry = Vec_IntEntryP( Vec_WecEntry(vInfo, a), i+1 );
                    *pEntry = Abc_MaxInt( *pEntry, Counter );
                }
                //printf( " %2d", Counter );
            }
            //printf( "\n" );
        }        
    }
    Vec_WecFree( vCofs );
    Vec_WecFree( vNodes );
    return vInfo;
}
Vec_Wec_t * Abc_NtkBddCollecInfo2( DdManager * dd, DdNode * aFunc )
{
    Vec_Wec_t * vInfo  = Vec_WecStart( dd->size*(dd->size-1)/2 );
    Vec_Wec_t * vNodes = Abc_NtkBddCollectInt( dd, aFunc );
    Vec_Wec_t * vCofs  = Abc_NtkBddCollectCofs( dd, aFunc, vNodes );
    Vec_Int_t * vLevel; int i, k, Obj, c = 0;
    for ( int a = 0;   a < dd->size; a++ ) 
    for ( int b = a+1; b < dd->size; b++ ) {
        Vec_Int_t * vInfo1 = Vec_WecEntry(vInfo, c++);
        word Sign = ((word)1 << a) | ((word)1 << b);
        for ( int n = 0; n < 4; n++ ) {
            word Value = ((word)(n & 1) << a) | ((word)((n >> 1) & 1) << b);
            Vec_WecForEachLevel( vNodes, vLevel, i )
                Vec_IntForEachEntry( vLevel, Obj, k )
                    Abc_Int2Bdd(aFunc, Obj)->Id = 0;
            aFunc->Id = 1;
            if ( n == 0 )
                Vec_IntPush( vInfo1, 1 );
            Vec_WecForEachLevelStop( vNodes, vLevel, i, dd->size ) {
                Vec_IntForEachEntry( vLevel, Obj, k ) {  
                    DdNode * aNode = Abc_Int2Bdd(aFunc, Obj);
                    if ( aNode->Id == 0 )
                        continue;
                    if ( !((Sign >> i) & 1) || ((Value >> i) & 1) == 0 )
                        cuddE(aNode)->Id |= 1;
                    if ( !((Sign >> i) & 1) || ((Value >> i) & 1) == 1 )
                        cuddT(aNode)->Id |= 1;
                }
                Vec_Int_t * vCof = Vec_WecEntry(vCofs, i+1);
                int Counter = 0;
                Vec_IntForEachEntry( vCof, Obj, k )
                    Counter += (int)Abc_Int2Bdd(aFunc, Obj)->Id;                
                if ( n == 0 )
                    Vec_IntPush( vInfo1, Counter );
                else {
                    int * pEntry = Vec_IntEntryP( vInfo1, i+1 );
                    *pEntry = Abc_MaxInt( *pEntry, Counter );
                }
            }
        }        
    }
    assert( c == Vec_WecSize(vInfo) );
    Vec_WecFree( vCofs );
    Vec_WecFree( vNodes );
    return vInfo;
}
Vec_Wec_t * Abc_NtkBddCollecInfo3( DdManager * dd, DdNode * aFunc )
{
    Vec_Wec_t * vInfo  = Vec_WecStart( dd->size*(dd->size-1)*(dd->size-2)/6 );
    Vec_Wec_t * vNodes = Abc_NtkBddCollectInt( dd, aFunc );
    Vec_Wec_t * vCofs  = Abc_NtkBddCollectCofs( dd, aFunc, vNodes );
    Vec_Int_t * vLevel; int i, k, Obj, d = 0;
    for ( int a = 0;   a < dd->size; a++ ) 
    for ( int b = a+1; b < dd->size; b++ ) 
    for ( int c = b+1; c < dd->size; c++ ) {
        Vec_Int_t * vInfo1 = Vec_WecEntry(vInfo, d++);
        word Sign = ((word)1 << a) | ((word)1 << b) | ((word)1 << c);
        for ( int n = 0; n < 8; n++ ) {
            word Value = ((word)(n & 1) << a) | ((word)((n >> 1) & 1) << b) | ((word)((n >> 2) & 1) << c);
            Vec_WecForEachLevel( vNodes, vLevel, i )
                Vec_IntForEachEntry( vLevel, Obj, k )
                    Abc_Int2Bdd(aFunc, Obj)->Id = 0;
            aFunc->Id = 1;
            if ( n == 0 )
                Vec_IntPush( vInfo1, 1 );
            Vec_WecForEachLevelStop( vNodes, vLevel, i, dd->size ) {
                Vec_IntForEachEntry( vLevel, Obj, k ) {  
                    DdNode * aNode = Abc_Int2Bdd(aFunc, Obj);
                    if ( aNode->Id == 0 )
                        continue;
                    if ( !((Sign >> i) & 1) || ((Value >> i) & 1) == 0 )
                        cuddE(aNode)->Id |= 1;
                    if ( !((Sign >> i) & 1) || ((Value >> i) & 1) == 1 )
                        cuddT(aNode)->Id |= 1;
                }
                Vec_Int_t * vCof = Vec_WecEntry(vCofs, i+1);
                int Counter = 0;
                Vec_IntForEachEntry( vCof, Obj, k )
                    Counter += (int)Abc_Int2Bdd(aFunc, Obj)->Id;                
                if ( n == 0 )
                    Vec_IntPush( vInfo1, Counter );
                else {
                    int * pEntry = Vec_IntEntryP( vInfo1, i+1 );
                    *pEntry = Abc_MaxInt( *pEntry, Counter );
                }
            }
        }        
    }
    assert( d == Vec_WecSize(vInfo) );
    Vec_WecFree( vCofs );
    Vec_WecFree( vNodes );
    return vInfo;
}
void Abc_NtkBddPrintInfo1( Vec_Wec_t * vInfo, Vec_Wec_t * vCofs )
{
    Vec_Int_t * vLevel; int i, k, Obj;
    printf( "Cofactor counts:\n" );
    printf( "     : " );
    Vec_WecForEachLevel( vCofs, vLevel, i )
        printf( " %2d", i );
    printf( "\n" );
    printf( "     : " );
    Vec_WecForEachLevel( vCofs, vLevel, i )
        printf( " %2d", Vec_IntSize(vLevel) );
    printf( "\n" );
    Vec_WecForEachLevel( vInfo, vLevel, i ) {
        printf( "%2d %c : ", i, 'a'+i );
        Vec_IntForEachEntry( vLevel, Obj, k )
            if ( k <= i )
                printf( "  -" );
            else
                printf( " %2d", Obj );
        printf( "\n" );
    }
}
void Abc_NtkBddPrintInfo2( Vec_Wec_t * vInfo, Vec_Wec_t * vCofs )
{
    Vec_Int_t * vLevel; int i, k, Obj;
    printf( "Cofactor counts:\n" );
    printf( "     : " );
    Vec_WecForEachLevel( vCofs, vLevel, i )
        printf( " %2d", i );
    printf( "\n" );    
    printf( "     : " );
    Vec_WecForEachLevel( vCofs, vLevel, i )
        printf( " %2d", Vec_IntSize(vLevel) );
    printf( "\n" );
    int c = 0, Limit = Vec_IntSize(Vec_WecEntry(vInfo, 0))-1;
    for ( int a = 0;   a < Limit; a++ ) 
    for ( int b = a+1; b < Limit; b++ ) {
        Vec_Int_t * vLevel = Vec_WecEntry(vInfo, c++);
        printf( "  %c%c : ", 'a'+a, 'a'+b );
        int Limit = Abc_MaxInt(a,b);
        Vec_IntForEachEntry( vLevel, Obj, k )
            if ( k <= Limit )
                printf( "  -" );
            else
                printf( " %2d", Obj );
        printf( "\n" );
    }
    assert( c == Vec_WecSize(vInfo) );
}
void Abc_NtkBddPrintInfo3( Vec_Wec_t * vInfo, Vec_Wec_t * vCofs )
{
    Vec_Int_t * vLevel; int i, k, Obj;
    printf( "Cofactor counts:\n" );
    printf( "     : " );
    Vec_WecForEachLevel( vCofs, vLevel, i )
        printf( " %2d", i );
    printf( "\n" );    
    printf( "     : " );
    Vec_WecForEachLevel( vCofs, vLevel, i )
        printf( " %2d", Vec_IntSize(vLevel) );
    printf( "\n" );
    int d = 0, Limit = Vec_IntSize(Vec_WecEntry(vInfo, 0))-1;
    for ( int a = 0;   a < Limit; a++ ) 
    for ( int b = a+1; b < Limit; b++ ) 
    for ( int c = b+1; c < Limit; c++ ) {
        Vec_Int_t * vLevel = Vec_WecEntry(vInfo, d++);
        printf( " %c%c%c : ", 'a'+a, 'a'+b, 'a'+c );
        int Limit = Abc_MaxInt(a,Abc_MaxInt(b,c));
        Vec_IntForEachEntry( vLevel, Obj, k )
            if ( k <= Limit )
                printf( "  -" );
            else
                printf( " %2d", Obj );
        printf( "\n" );
    }
    assert( d == Vec_WecSize(vInfo) );
}

void Abc_NtkBddDecExploreOne( DdManager * dd, DdNode * bFunc, int iOrder )
{
    DdManager * ddNew = Cudd_Init( dd->size, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
    int i, * pProfile = ABC_CALLOC( int, dd->size + 100 );
    Cudd_AutodynEnable( ddNew,  CUDD_REORDER_SYMM_SIFT );
    Vec_Int_t * vPerm = Vec_IntStartNatural( dd->size ); if ( iOrder ) Vec_IntRandomizeOrder( vPerm );
    Vec_Int_t * vPermInv = Vec_IntInvert( vPerm, -1 );
    DdNode * bFuncNew = Extra_TransferPermute( dd, ddNew, bFunc, Vec_IntArray(vPerm) ); Cudd_Ref(bFuncNew);
    if ( iOrder ) Cudd_ReduceHeap( ddNew, CUDD_REORDER_SYMM_SIFT, 1 );
    Vec_IntFree( vPerm );
    DdNode * aFuncNew = Cudd_BddToAdd( ddNew, bFuncNew ); Cudd_Ref( aFuncNew );
    //Extra_ProfileWidth( ddNew, aFuncNew, pProfile, -1 );
    if ( iOrder )
        printf( "Random order %2d: ", iOrder );
    else
        printf( "Natural order:   " );
    printf( "BDD size = %3d  ", Cudd_DagSize(aFuncNew) );
    for ( i = 0; i < dd->size; i++ )
        printf( " %c", 'a' + Vec_IntEntry(vPermInv, ddNew->invperm[i]) );
    printf( "\n" );
    //Abc_NtkBddTestProfile( ddNew, aFuncNew );

    Vec_Wec_t * vNodes = Abc_NtkBddCollectInt( ddNew, aFuncNew );
    printf( "Nodes by level:\n" );
    Vec_WecPrint( vNodes, 0 );
    Vec_Wec_t * vCofs = Abc_NtkBddCollectCofs( ddNew, aFuncNew, vNodes );
    printf( "Cofactors by level:\n" );
    Vec_WecPrint( vCofs, 0 );
    Vec_Wec_t * vInfo1 = Abc_NtkBddCollecInfo1( ddNew, aFuncNew );
    Abc_NtkBddPrintInfo1( vInfo1, vCofs );
    Vec_Wec_t * vInfo2 = Abc_NtkBddCollecInfo2( ddNew, aFuncNew );
    Abc_NtkBddPrintInfo2( vInfo2, vCofs );
    Vec_Wec_t * vInfo3 = Abc_NtkBddCollecInfo3( ddNew, aFuncNew );
    Abc_NtkBddPrintInfo3( vInfo3, vCofs );
    printf( "\n" );
    Vec_WecFree( vNodes );
    Vec_WecFree( vCofs );
    Vec_WecFree( vInfo1 );
    Vec_WecFree( vInfo2 );
    Vec_WecFree( vInfo3 );

    Cudd_RecursiveDeref( ddNew, aFuncNew );
    Cudd_RecursiveDeref( ddNew, bFuncNew );
    Cudd_Quit( ddNew );
    ABC_FREE( pProfile );
}
void Abc_NtkBddDecExplore( Abc_Obj_t * pNode )
{
    DdManager * dd = (DdManager *)pNode->pNtk->pManFunc;
    DdNode * bFunc = (DdNode *)pNode->pData;
    int i; Abc_Random(1);
    if ( Abc_ObjIsNode(pNode) )
        for ( i = 0; i < 4; i++ )
            Abc_NtkBddDecExploreOne( dd, bFunc, i );
}

/**Function*************************************************************

  Synopsis    [Decompose the function once.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Obj_t * Abc_NtkBddDecompose( Abc_Ntk_t * pNtkNew, Abc_Obj_t * pNode, int nLutSize, int fVerbose )
{
    Vec_Ptr_t * vCofs, * vUniq;
    DdManager * dd = (DdManager *)pNode->pNtk->pManFunc;
    DdNode * bCof;
    Abc_Obj_t * pNodeNew = NULL;
    Abc_Obj_t * pCofs[20];
    int i;
    assert( Abc_ObjFaninNum(pNode) > nLutSize );
    // try to decompose with two LUTs (the best case for Supp = LutSize + 1)
    if ( Abc_ObjFaninNum(pNode) == nLutSize + 1 )
    {

        pNodeNew = Abc_NtkBddFindCofactor( pNtkNew, pNode, nLutSize );
        if ( pNodeNew != NULL )
        {
            if ( fVerbose )
            printf( "Decomposing %d-input node %d using MUX.\n",
                Abc_ObjFaninNum(pNode), Abc_ObjId(pNode) );
            return pNodeNew;
        }

    }
    // cofactor w.r.t. the bound set variables
    vCofs = Abc_NtkBddCofactors( dd, (DdNode *)pNode->pData, nLutSize );
    vUniq = Vec_PtrDup( vCofs );
    Vec_PtrUniqify( vUniq, (int (*)(const void *, const void *))Vec_PtrSortCompare );
    // only perform decomposition which it is support reducing with two less vars
    if( Vec_PtrSize(vUniq) > (1 << (nLutSize-2)) )
    {
        Vec_PtrFree( vCofs );
        vCofs = Abc_NtkBddCofactors( dd, (DdNode *)pNode->pData, 2 );
        if ( fVerbose )
        printf( "Decomposing %d-input node %d using cofactoring with %d cofactors (myu = %d).\n",
            Abc_ObjFaninNum(pNode), Abc_ObjId(pNode), Vec_PtrSize(vCofs), Vec_PtrSize(vUniq) );
        // implement the cofactors
        pCofs[0] = Abc_ObjFanin(pNode, 0)->pCopy;
        pCofs[1] = Abc_ObjFanin(pNode, 1)->pCopy;
        Vec_PtrForEachEntry( DdNode *, vCofs, bCof, i )
            pCofs[2+i] = Abc_NtkCreateCofLut( pNtkNew, dd, bCof, pNode, 2 );
        if ( nLutSize == 4 )
            pNodeNew = Abc_NtkBddMux412( pNtkNew, pCofs );
        else if ( nLutSize == 5 )
            pNodeNew = Abc_NtkBddMux412a( pNtkNew, pCofs );
        else if ( nLutSize == 6 )
            pNodeNew = Abc_NtkBddMux411( pNtkNew, pCofs );
        else  assert( 0 );
    }
    // alternative decompose using MUX-decomposition
    else
    {
        if ( fVerbose )
        printf( "Decomposing %d-input node %d using Curtis with %d unique columns.\n",
            Abc_ObjFaninNum(pNode), Abc_ObjId(pNode), Vec_PtrSize(vUniq) );
        pNodeNew = Abc_NtkBddCurtis( pNtkNew, pNode, vCofs, vUniq );
    }
    Vec_PtrFree( vCofs );
    Vec_PtrFree( vUniq );
    return pNodeNew;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkLutminConstruct( Abc_Ntk_t * pNtkClp, Abc_Ntk_t * pNtkDec, int nLutSize, int fVerbose )
{
    Vec_Ptr_t * vNodes;
    Abc_Obj_t * pNode, * pFanin;
    int i, k;
    vNodes = Abc_NtkDfs( pNtkClp, 0 );
    Vec_PtrForEachEntry( Abc_Obj_t *, vNodes, pNode, i )
    {
        if ( Abc_ObjFaninNum(pNode) <= nLutSize )
        {
            pNode->pCopy = Abc_NtkDupObj( pNtkDec, pNode, 0 );
            Abc_ObjForEachFanin( pNode, pFanin, k )
                Abc_ObjAddFanin( pNode->pCopy, pFanin->pCopy );
        }
        else
            pNode->pCopy = Abc_NtkBddDecompose( pNtkDec, pNode, nLutSize, fVerbose );
    }
    Vec_PtrFree( vNodes );
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkLutminInt( Abc_Ntk_t * pNtk, int nLutSize, int fReorder, int fVerbose )
{
    extern void Abc_NtkBddReorder( Abc_Ntk_t * pNtk, int fVerbose );
    Abc_Ntk_t * pNtkDec;
    // minimize BDDs
    if ( fReorder )
        Abc_NtkBddReorder( pNtk, 0 );
    // decompose one output at a time
    pNtkDec = Abc_NtkStartFrom( pNtk, ABC_NTK_LOGIC, ABC_FUNC_BDD );
    // make sure the new manager has enough inputs
    Cudd_bddIthVar( (DdManager *)pNtkDec->pManFunc, Abc_NtkGetFaninMax(pNtk) );
    // put the results into the new network (save new CO drivers in old CO drivers)
    Abc_NtkLutminConstruct( pNtk, pNtkDec, nLutSize, fVerbose );
    // finalize the new network
    Abc_NtkFinalize( pNtk, pNtkDec );
    // make the network minimum base
    Abc_NtkMinimumBase( pNtkDec );
    return pNtkDec;
}

/**Function*************************************************************

  Synopsis    [Performs minimum-LUT decomposition of the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkLutmin( Abc_Ntk_t * pNtkInit, int nLutSize, int fReorder, int fVerbose )
{
    extern int Abc_NtkFraigSweep( Abc_Ntk_t * pNtk, int fUseInv, int fExdc, int fVerbose, int fVeryVerbose );
    Abc_Ntk_t * pNtkNew, * pTemp;
    int i;
    if ( nLutSize < 4 )
    {
        printf( "The LUT count (%d) should be at least 4.\n", nLutSize );
        return NULL;
    }
    if ( nLutSize > 6 )
    {
        printf( "The LUT count (%d) should not exceed 6.\n", nLutSize );
        return NULL;
    }
    // create internal representation
    if ( Abc_NtkIsStrash(pNtkInit) )
        pNtkNew = Abc_NtkDup( pNtkInit );
    else
        pNtkNew = Abc_NtkStrash( pNtkInit, 0, 1, 0 );
    // collapse the network 
    pNtkNew = Abc_NtkCollapse( pTemp = pNtkNew, 10000, 0, fReorder, 0, 0, 0 );
    Abc_NtkDelete( pTemp );
    if ( pNtkNew == NULL )
        return NULL;
    // convert it to BDD
    if ( !Abc_NtkIsBddLogic(pNtkNew) )
        Abc_NtkToBdd( pNtkNew );
    // iterate decomposition
    for ( i = 0; Abc_NtkGetFaninMax(pNtkNew) > nLutSize; i++ )
    {
        if ( fVerbose )
            printf( "*** Iteration %d:\n", i+1 );
        if ( fVerbose )
            printf( "Decomposing network with %d nodes and %d max fanin count for K = %d.\n", 
                Abc_NtkNodeNum(pNtkNew), Abc_NtkGetFaninMax(pNtkNew), nLutSize );
        pNtkNew = Abc_NtkLutminInt( pTemp = pNtkNew, nLutSize, fReorder, fVerbose );
        Abc_NtkDelete( pTemp );
    }
    // fix the problem with complemented and duplicated CO edges
    Abc_NtkLogicMakeSimpleCos( pNtkNew, 0 );
    // merge functionally equivalent nodes
    Abc_NtkFraigSweep( pNtkNew, 1, 0, 0, 0 );
    // make sure everything is okay
    if ( !Abc_NtkCheck( pNtkNew ) )
    {
        printf( "Abc_NtkLutmin: The network check has failed.\n" );
        return 0;
    }
    return pNtkNew;
}

#else

Abc_Ntk_t * Abc_NtkLutmin( Abc_Ntk_t * pNtkInit, int nLutSize, int fReorder, int fVerbose ) { return NULL; }
void Abc_NtkBddDecExplore( Abc_Obj_t * pNode ) {}

#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

