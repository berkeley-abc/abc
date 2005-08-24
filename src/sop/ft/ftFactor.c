/**CFile****************************************************************

  FileName    [ftFactor.c]

  PackageName [MVSIS 2.0: Multi-valued logic synthesis system.]

  Synopsis    [Procedures for algebraic factoring.]

  Author      [MVSIS Group]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - February 1, 2003.]

  Revision    [$Id: ftFactor.c,v 1.3 2003/09/01 04:56:43 alanmi Exp $]

***********************************************************************/

#include "abc.h"
#include "mvc.h"
#include "ft.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// the types of nodes in FFs
enum { FT_NODE_NONE, FT_NODE_AND, FT_NODE_OR, FT_NODE_INV, FT_NODE_LEAF, FT_NODE_0, FT_NODE_1 };

static Ft_Node_t *       Ft_Factor_rec( Vec_Int_t * vForm, Mvc_Cover_t * pCover );
static Ft_Node_t *       Ft_FactorLF_rec( Vec_Int_t * vForm, Mvc_Cover_t * pCover, Mvc_Cover_t * pSimple );

static Ft_Node_t *       Ft_FactorTrivial( Vec_Int_t * vForm, Mvc_Cover_t * pCover );
static Ft_Node_t *       Ft_FactorTrivialCube( Vec_Int_t * vForm, Mvc_Cover_t * pCover, Mvc_Cube_t * pCube );
static Ft_Node_t *       Ft_FactorTrivialTree_rec( Vec_Int_t * vForm, Ft_Node_t ** ppNodes, int nNodes, int fAnd );
static Ft_Node_t *       Ft_FactorTrivialCascade( Vec_Int_t * vForm, Mvc_Cover_t * pCover );
static Ft_Node_t *       Ft_FactorTrivialCubeCascade( Vec_Int_t * vForm, Mvc_Cover_t * pCover, Mvc_Cube_t * pCube );

static Ft_Node_t *       Ft_FactorNodeCreate( Vec_Int_t * vForm, int Type, Ft_Node_t * pNode1, Ft_Node_t * pNode2 );
static Ft_Node_t *       Ft_FactorLeafCreate( Vec_Int_t * vForm, int iLit );
static void              Ft_FactorFinalize( Vec_Int_t * vForm, Ft_Node_t * pNode, int nVars );
static Vec_Int_t *       Ft_FactorConst( int fConst1 );

// temporary procedures that work with the covers
static Mvc_Cover_t *     Ft_ConvertSopToMvc( char * pSop );
static int               Ft_FactorVerify( char * pSop, Vec_Int_t * vForm );

// temporary managers
static Mvc_Manager_t *   pMem = NULL;
static DdManager *       dd = NULL;
 
////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Factors the cover.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Ft_Factor( char * pSop )
{
    Vec_Int_t * vForm;
    Ft_Node_t * pNode;
    Mvc_Cover_t * pCover;
    int nVars = Abc_SopGetVarNum( pSop );

    // derive the cover from the SOP representation
    pCover = Ft_ConvertSopToMvc( pSop );

    // make sure the cover is CCS free (should be done before CST)
    Mvc_CoverContain( pCover );
    // check for trivial functions
    if ( Mvc_CoverIsEmpty(pCover) )
    {
        Mvc_CoverFree( pCover );
        return Ft_FactorConst( 0 );
    }
    if ( Mvc_CoverIsTautology(pCover) )
    {
        Mvc_CoverFree( pCover );
        return Ft_FactorConst( 1 );
    }

    // perform CST
    Mvc_CoverInverse( pCover ); // CST

    // start the factored form
    vForm = Vec_IntAlloc( 1000 );
    Vec_IntFill( vForm, nVars, 0 );
    // factor the cover
    pNode = Ft_Factor_rec( vForm, pCover );
    // finalize the factored form
    Ft_FactorFinalize( vForm, pNode, nVars );
    // check if the cover was originally complented
    if ( Abc_SopGetPhase(pSop) == 0 )
        Ft_FactorComplement( vForm );

    // verify the factored form
//    if ( !Ft_FactorVerify( pSop, vForm ) )
//        printf( "Verification has failed.\n" );

//    Mvc_CoverInverse( pCover ); // undo CST
    Mvc_CoverFree( pCover );
    return vForm;
}

/**Function*************************************************************

  Synopsis    [Internal recursive factoring procedure.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ft_Node_t * Ft_Factor_rec( Vec_Int_t * vForm, Mvc_Cover_t * pCover )
{
    Mvc_Cover_t * pDiv, * pQuo, * pRem, * pCom;
    Ft_Node_t * pNodeDiv, * pNodeQuo, * pNodeRem;
    Ft_Node_t * pNodeAnd, * pNode;

    // make sure the cover contains some cubes
    assert( Mvc_CoverReadCubeNum(pCover) );

    // get the divisor
    pDiv = Mvc_CoverDivisor( pCover );
    if ( pDiv == NULL )
        return Ft_FactorTrivial( vForm, pCover );

    // divide the cover by the divisor
    Mvc_CoverDivideInternal( pCover, pDiv, &pQuo, &pRem );
    assert( Mvc_CoverReadCubeNum(pQuo) );

    Mvc_CoverFree( pDiv );
    Mvc_CoverFree( pRem );

    // check the trivial case
    if ( Mvc_CoverReadCubeNum(pQuo) == 1 )
    {
        pNode = Ft_FactorLF_rec( vForm, pCover, pQuo );
        Mvc_CoverFree( pQuo );
        return pNode;
    }

    // make the quotient cube free
    Mvc_CoverMakeCubeFree( pQuo );

    // divide the cover by the quotient
    Mvc_CoverDivideInternal( pCover, pQuo, &pDiv, &pRem );

    // check the trivial case
    if ( Mvc_CoverIsCubeFree( pDiv ) )
    {
        pNodeDiv = Ft_Factor_rec( vForm, pDiv );
        pNodeQuo = Ft_Factor_rec( vForm, pQuo );
        Mvc_CoverFree( pDiv );
        Mvc_CoverFree( pQuo );
        pNodeAnd = Ft_FactorNodeCreate( vForm, FT_NODE_AND, pNodeDiv, pNodeQuo );
        if ( Mvc_CoverReadCubeNum(pRem) == 0 )
        {
            Mvc_CoverFree( pRem );
            return pNodeAnd;
        }
        else
        {
            pNodeRem = Ft_Factor_rec( vForm, pRem );
            Mvc_CoverFree( pRem );
            return Ft_FactorNodeCreate( vForm, FT_NODE_OR,  pNodeAnd, pNodeRem );
        }
    }

    // get the common cube
    pCom = Mvc_CoverCommonCubeCover( pDiv );
    Mvc_CoverFree( pDiv );
    Mvc_CoverFree( pQuo );
    Mvc_CoverFree( pRem );

    // solve the simple problem
    pNode = Ft_FactorLF_rec( vForm, pCover, pCom );
    Mvc_CoverFree( pCom );
    return pNode;
}


/**Function*************************************************************

  Synopsis    [Internal recursive factoring procedure for the leaf case.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ft_Node_t * Ft_FactorLF_rec( Vec_Int_t * vForm, Mvc_Cover_t * pCover, Mvc_Cover_t * pSimple )
{
    Mvc_Cover_t * pDiv, * pQuo, * pRem;
    Ft_Node_t * pNodeDiv, * pNodeQuo, * pNodeRem;
    Ft_Node_t * pNodeAnd;

    // get the most often occurring literal
    pDiv = Mvc_CoverBestLiteralCover( pCover, pSimple );
    // divide the cover by the literal
    Mvc_CoverDivideByLiteral( pCover, pDiv, &pQuo, &pRem );
    // get the node pointer for the literal
    pNodeDiv = Ft_FactorTrivialCube( vForm, pDiv, Mvc_CoverReadCubeHead(pDiv) );
    Mvc_CoverFree( pDiv );
    // factor the quotient and remainder
    pNodeQuo = Ft_Factor_rec( vForm, pQuo );
    Mvc_CoverFree( pQuo );
    pNodeAnd = Ft_FactorNodeCreate( vForm, FT_NODE_AND, pNodeDiv, pNodeQuo );
    if ( Mvc_CoverReadCubeNum(pRem) == 0 )
    {
        Mvc_CoverFree( pRem );
        return pNodeAnd;
    }
    else
    {
        pNodeRem = Ft_Factor_rec( vForm, pRem );
        Mvc_CoverFree( pRem );
        return Ft_FactorNodeCreate( vForm, FT_NODE_OR,  pNodeAnd, pNodeRem );
    }
}



/**Function*************************************************************

  Synopsis    [Factoring the cover, which has no algebraic divisors.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ft_Node_t * Ft_FactorTrivial( Vec_Int_t * vForm, Mvc_Cover_t * pCover )
{
    Ft_Node_t ** ppNodes;
    Ft_Node_t * pNode;
    Mvc_Cube_t * pCube;
    int i, nNodes;

    // create space to put the cubes
    nNodes = Mvc_CoverReadCubeNum(pCover);
    assert( nNodes > 0 );
    ppNodes = ALLOC( Ft_Node_t *, nNodes );
    // create the factored form for each cube
    i = 0;
    Mvc_CoverForEachCube( pCover, pCube )
        ppNodes[i++] = Ft_FactorTrivialCube( vForm, pCover, pCube );
    assert( i == nNodes );
    // balance the factored forms
    pNode = Ft_FactorTrivialTree_rec( vForm, ppNodes, nNodes, 0 );
    free( ppNodes );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Factoring the cube.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ft_Node_t * Ft_FactorTrivialCube( Vec_Int_t * vForm, Mvc_Cover_t * pCover, Mvc_Cube_t * pCube )
{
    Ft_Node_t ** ppNodes;
    Ft_Node_t * pNode;
    int iBit, Value, i;

    // create space to put each literal
    ppNodes = ALLOC( Ft_Node_t *, pCover->nBits );
    // create the factored form for each literal
    i = 0;
    Mvc_CubeForEachBit( pCover, pCube, iBit, Value )
    {
        if ( Value )
            ppNodes[i++] = Ft_FactorLeafCreate( vForm, iBit );
    }
    assert( i > 0 && i < pCover->nBits );
    // balance the factored forms
    pNode = Ft_FactorTrivialTree_rec( vForm, ppNodes, i, 1 );
    free( ppNodes );
    return pNode;
}
 
/**Function*************************************************************

  Synopsis    [Create the well-balanced tree of nodes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ft_Node_t * Ft_FactorTrivialTree_rec( Vec_Int_t * vForm, Ft_Node_t ** ppNodes, int nNodes, int fAnd )
{
    Ft_Node_t * pNode1, * pNode2;
    int nNodes1, nNodes2;

    if ( nNodes == 1 )
        return ppNodes[0];

    // split the nodes into two parts
    nNodes2 = nNodes/2;
    nNodes1 = nNodes - nNodes2;

    // recursively construct the tree for the parts
    pNode1 = Ft_FactorTrivialTree_rec( vForm, ppNodes,           nNodes1, fAnd );
    pNode2 = Ft_FactorTrivialTree_rec( vForm, ppNodes + nNodes1, nNodes2, fAnd );

    return Ft_FactorNodeCreate( vForm, fAnd? FT_NODE_AND : FT_NODE_OR, pNode1, pNode2 );
}



/**Function*************************************************************

  Synopsis    [Factoring the cover, which has no algebraic divisors.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ft_Node_t * Ft_FactorTrivialCascade( Vec_Int_t * vForm, Mvc_Cover_t * pCover )
{
    Ft_Node_t * pNode;
    Mvc_Cube_t * pCube;

    // iterate through the cubes
    pNode = NULL;
    Mvc_CoverForEachCube( pCover, pCube )
    {
        if ( pNode == NULL )
            pNode = Ft_FactorTrivialCube( vForm, pCover, pCube );
        else
            pNode = Ft_FactorNodeCreate( vForm, FT_NODE_OR, pNode, Ft_FactorTrivialCubeCascade( vForm, pCover, pCube ) );
    }
    assert( pNode ); // if this assertion fails, the input cover is not SCC-free
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Factoring the cube.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ft_Node_t * Ft_FactorTrivialCubeCascade( Vec_Int_t * vForm, Mvc_Cover_t * pCover, Mvc_Cube_t * pCube )
{
    Ft_Node_t * pNode;
    int iBit, Value;

    // iterate through the literals
    pNode = NULL;
    Mvc_CubeForEachBit( pCover, pCube, iBit, Value )
    {
        if ( Value )
        {
            if ( pNode == NULL )
                pNode = Ft_FactorLeafCreate( vForm, iBit );
            else
                pNode = Ft_FactorNodeCreate( vForm, FT_NODE_AND, pNode, Ft_FactorLeafCreate( vForm, iBit ) );
        }
    }
    assert( pNode ); // if this assertion fails, the input cover is not SCC-free
    return pNode;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ft_Node_t * Ft_FactorNodeCreate( Vec_Int_t * vForm, int Type, Ft_Node_t * pNode1, Ft_Node_t * pNode2 )
{
    Ft_Node_t * pNode;
    // get the new node
    Vec_IntPush( vForm, 0 );
    pNode = Ft_NodeReadLast( vForm );
    // set the inputs and other info
    pNode->iFanin0 = (Ft_Node_t *)Ptr_Regular(pNode1) - (Ft_Node_t *)vForm->pArray;
    pNode->iFanin1 = (Ft_Node_t *)Ptr_Regular(pNode2) - (Ft_Node_t *)vForm->pArray;
    assert( pNode->iFanin0 < (unsigned)vForm->nSize );
    assert( pNode->iFanin1 < (unsigned)vForm->nSize );
    pNode->fIntern = 1;
    pNode->fCompl  = 0;
    pNode->fConst  = 0;
    pNode->fEdge0  = Ptr_IsComplement(pNode1);
    pNode->fEdge1  = Ptr_IsComplement(pNode2);
    // consider specific gates
    if ( Type == FT_NODE_OR )
    {
        pNode->fCompl0 = !Ptr_IsComplement(pNode1);
        pNode->fCompl1 = !Ptr_IsComplement(pNode2);
        pNode->fNodeOr = 1;
        return Ptr_Not( pNode );
    }
    if ( Type == FT_NODE_AND )
    {
        pNode->fCompl0 = Ptr_IsComplement(pNode1);
        pNode->fCompl1 = Ptr_IsComplement(pNode2);
        pNode->fNodeOr = 0;
        return pNode;
    }
    assert( 0 );
    return NULL;

/*
    Vec_Int_t * vForm;
    assert( pNode1 && pNode2 );
    pNode = MEM_ALLOC( vForm->pMem, void, 1 );
    memset( pNode, 0, sizeof(void) );
    pNode->Type = Type;
    pNode->pOne = pNode1;
    pNode->pTwo = pNode2;
    // update FF statistics
    if ( pNode->Type == FT_NODE_LEAF )
        vForm->nNodes++;
    return pNode;
*/
}

/**Function*************************************************************

  Synopsis    [Factoring the cube.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Ft_Node_t * Ft_FactorLeafCreate( Vec_Int_t * vForm, int iLit )
{
    return Ptr_NotCond( Ft_NodeRead(vForm, iLit/2), iLit%2 ); // using CST

/*
    Vm_VarMap_t * pVm;
    int * pValuesFirst, * pValues;
    int nValuesIn, nVarsIn;
    Vec_Int_t * vForm;
    int iVar;
    pVm = vForm->pVm;
    pValues      = Vm_VarMapReadValuesArray(pVm);
    pValuesFirst = Vm_VarMapReadValuesFirstArray(pVm);
    nValuesIn    = Vm_VarMapReadValuesInNum(pVm);
    nVarsIn      = Vm_VarMapReadVarsInNum(pVm);
    assert( iLit < nValuesIn );
    for ( iVar = 0; iVar < nVarsIn; iVar++ )
        if ( iLit < pValuesFirst[iVar] + pValues[iVar] )
            break;
    assert( iVar < nVarsIn );
    pNode = Ft_FactorNodeCreate( vForm, FT_NODE_LEAF, NULL, NULL );
    pNode->VarNum  = iVar;
    pNode->nValues = pValues[iVar];
    pNode->uData   = FT_MV_MASK(pNode->nValues) ^ (1 << (iLit - pValuesFirst[iVar]));
    return pNode;
*/
}


/**Function*************************************************************

  Synopsis    [Adds a single-variable literal if necessary.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ft_FactorFinalize( Vec_Int_t * vForm, Ft_Node_t * pRoot, int nVars )
{
    Ft_Node_t * pRootR = Ptr_Regular(pRoot);
    int iNode = pRootR - (Ft_Node_t *)vForm->pArray;
    Ft_Node_t * pNode;
    if ( iNode >= nVars )
    {
        // set the complemented attribute
        pRootR->fCompl = Ptr_IsComplement(pRoot);
        return;
    }
    // create a new node
    Vec_IntPush( vForm, 0 );
    pNode = Ft_NodeReadLast( vForm );
    pNode->iFanin0 = iNode;
    pNode->iFanin1 = iNode;
    pNode->fIntern = 1;
    pNode->fCompl  = Ptr_IsComplement(pRoot);
}

/**Function*************************************************************

  Synopsis    [Computes the number of variables in the factored form.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ft_FactorGetNumVars( Vec_Int_t * vForm )
{
    int i;
    for ( i = 0; i < vForm->nSize; i++ )
        if ( vForm->pArray[i] )
            break;
    return i;
}

/**Function*************************************************************

  Synopsis    [Computes the number of variables in the factored form.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ft_FactorGetNumNodes( Vec_Int_t * vForm )
{
    Ft_Node_t * pNode;
    int i;
    pNode = Ft_NodeReadLast(vForm);
    if ( pNode->fConst )
        return 0;
    if ( !pNode->fConst && pNode->iFanin0 == pNode->iFanin1 ) // literal
        return 1;
    for ( i = 0; i < vForm->nSize; i++ )
        if ( vForm->pArray[i] )
            break;
    return vForm->nSize - i + 1;
}

/**Function*************************************************************

  Synopsis    [Complements the factored form.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ft_FactorComplement( Vec_Int_t * vForm )
{
    Ft_Node_t * pNode;
    pNode = Ft_NodeReadLast(vForm);
    pNode->fCompl ^= 1;
}

/**Function*************************************************************

  Synopsis    [Creates a constant 0 or 1 factored form.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Vec_Int_t * Ft_FactorConst( int fConst1 )
{
    Vec_Int_t * vForm;
    Ft_Node_t * pNode;
    // create the constant node
    vForm = Vec_IntAlloc( 1 );
    Vec_IntPush( vForm, 0 );
    pNode = Ft_NodeReadLast( vForm );
    pNode->fIntern = 1;
    pNode->fConst  = 1;
    pNode->fCompl  = !fConst1;
    return vForm;
}






/**Function*************************************************************

  Synopsis    [Start the MVC manager used in the factoring package.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ft_FactorStartMan()
{
    assert( pMem == NULL );
    pMem = Mvc_ManagerStart();
    dd = Cudd_Init( 0, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );
}

/**Function*************************************************************

  Synopsis    [Stops the MVC maanager used in the factoring package.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Ft_FactorStopMan()
{
    assert( pMem );
    Mvc_ManagerFree( pMem );
    Cudd_Quit( dd );
    pMem = NULL;
    dd = NULL;
}





/**Function*************************************************************

  Synopsis    [Converts SOP into MVC.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Mvc_Cover_t * Ft_ConvertSopToMvc( char * pSop )
{
    Mvc_Cover_t * pMvc;
    Mvc_Cube_t * pMvcCube;
    char * pCube;
    int nVars, Value, v;

    // start the cover
    nVars = Abc_SopGetVarNum(pSop);
    pMvc = Mvc_CoverAlloc( pMem, nVars * 2 );
    // check the logic function of the node
    Abc_SopForEachCube( pSop, nVars, pCube )
    {
        // create and add the cube
        pMvcCube = Mvc_CubeAlloc( pMvc );
        Mvc_CoverAddCubeTail( pMvc, pMvcCube );
        // fill in the literals
        Mvc_CubeBitFill( pMvcCube );
        Abc_CubeForEachVar( pCube, Value, v )
        {
            if ( Value == '0' )
                Mvc_CubeBitRemove( pMvcCube, v * 2 + 1 );
            else if ( Value == '1' )
                Mvc_CubeBitRemove( pMvcCube, v * 2 );
        }
    }
//Mvc_CoverPrint( pMvc );
    return pMvc;
}



/**Function*************************************************************

  Synopsis    [Converts SOP into BDD.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Ft_ConvertSopToBdd( DdManager * dd, char * pSop )
{
    DdNode * bSum, * bCube, * bTemp, * bVar;
    char * pCube;
    int nVars, Value, v;
    // start the cover
    nVars = Abc_SopGetVarNum(pSop);
    // check the logic function of the node
    bSum = Cudd_ReadLogicZero(dd);   Cudd_Ref( bSum );
    Abc_SopForEachCube( pSop, nVars, pCube )
    {
        bCube = Cudd_ReadOne(dd);   Cudd_Ref( bCube );
        Abc_CubeForEachVar( pCube, Value, v )
        {
            if ( Value == '0' )
                bVar = Cudd_Not( Cudd_bddIthVar( dd, v ) );
            else if ( Value == '1' )
                bVar = Cudd_bddIthVar( dd, v );
            else
                continue;
            bCube  = Cudd_bddAnd( dd, bTemp = bCube, bVar );   Cudd_Ref( bCube );
            Cudd_RecursiveDeref( dd, bTemp );
        }
        bSum = Cudd_bddOr( dd, bTemp = bSum, bCube );   Cudd_Ref( bSum );
        Cudd_RecursiveDeref( dd, bTemp );
        Cudd_RecursiveDeref( dd, bCube );
    }
    // complement the result if necessary
    bSum = Cudd_NotCond( bSum, !Abc_SopGetPhase(pSop) );
    Cudd_Deref( bSum );
    return bSum;
}

/**Function*************************************************************

  Synopsis    [Converts SOP into BDD.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Ft_ConvertFormToBdd( DdManager * dd, Vec_Int_t * vForm )
{
    Vec_Ptr_t * vFuncs;
    DdNode * bFunc, * bFunc0, * bFunc1;
    Ft_Node_t * pNode;
    int i, nVars;

    // sanity checks
    nVars = Ft_FactorGetNumVars( vForm );
    assert( nVars >= 0 );
    assert( vForm->nSize > nVars );

    // check for constant function
    pNode = Ft_NodeRead( vForm, 0 );
    if ( pNode->fConst )
        return Cudd_NotCond( dd->one, pNode->fCompl );

    // start the array of elementary variables
    vFuncs = Vec_PtrAlloc( 20 );
    for ( i = 0; i < nVars; i++ )
        Vec_PtrPush( vFuncs, Cudd_bddIthVar(dd, i) );

    // compute the functions of other nodes
    for ( i = nVars; i < vForm->nSize; i++ )
    {
        pNode  = Ft_NodeRead( vForm, i );
        bFunc0 = Cudd_NotCond( vFuncs->pArray[pNode->iFanin0], pNode->fCompl0 ); 
        bFunc1 = Cudd_NotCond( vFuncs->pArray[pNode->iFanin1], pNode->fCompl1 ); 
        bFunc  = Cudd_bddAnd( dd, bFunc0, bFunc1 );   Cudd_Ref( bFunc );
        Vec_PtrPush( vFuncs, bFunc );
    }
    assert( vForm->nSize = vFuncs->nSize );

    // deref the intermediate results
    for ( i = nVars; i < vForm->nSize-1; i++ )
        Cudd_RecursiveDeref( dd, (DdNode *)vFuncs->pArray[i] );
    Vec_PtrFree( vFuncs );

    // complement the result if necessary
    pNode = Ft_NodeReadLast( vForm );
    bFunc = Cudd_NotCond( bFunc, pNode->fCompl );

    // return the result
    Cudd_Deref( bFunc );
    return bFunc;
}


/**Function*************************************************************

  Synopsis    [Verifies that the factoring is correct.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Ft_FactorVerify( char * pSop, Vec_Int_t * vForm )
{
    DdNode * bFunc1, * bFunc2;
    int RetValue;
    bFunc1 = Ft_ConvertSopToBdd( dd, pSop );    Cudd_Ref( bFunc1 );
    bFunc2 = Ft_ConvertFormToBdd( dd, vForm );  Cudd_Ref( bFunc2 );
//Extra_bddPrint( dd, bFunc1 ); printf("\n");
//Extra_bddPrint( dd, bFunc2 ); printf("\n");
    RetValue = (bFunc1 == bFunc2);
    Cudd_RecursiveDeref( dd, bFunc1 );
    Cudd_RecursiveDeref( dd, bFunc2 );
    return RetValue;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


