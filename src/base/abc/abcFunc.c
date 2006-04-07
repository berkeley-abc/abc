/**CFile****************************************************************

  FileName    [abcFunc.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Transformations between different functionality representations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcFunc.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define ABC_MUX_CUBES   100000

static int         Abc_ConvertZddToSop( DdManager * dd, DdNode * zCover, char * pSop, int nFanins, Vec_Str_t * vCube, int fPhase );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Converts the network from SOP to BDD representation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkSopToBdd( Abc_Ntk_t * pNtk )
{
    Abc_Obj_t * pNode;
    DdManager * dd;
    int nFaninsMax, i;

    assert( Abc_NtkIsSopLogic(pNtk) ); 

    // start the functionality manager
    nFaninsMax = Abc_NtkGetFaninMax( pNtk );
    if ( nFaninsMax == 0 )
        printf( "Warning: The network has only constant nodes.\n" );

    dd = Cudd_Init( nFaninsMax, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );

    // convert each node from SOP to BDD
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        assert( pNode->pData );
        pNode->pData = Abc_ConvertSopToBdd( dd, pNode->pData );
        if ( pNode->pData == NULL )
        {
            printf( "Abc_NtkSopToBdd: Error while converting SOP into BDD.\n" );
            return 0;
        }
        Cudd_Ref( pNode->pData );
    }

    Extra_MmFlexStop( pNtk->pManFunc, 0 );
    pNtk->pManFunc = dd;

    // update the network type
    pNtk->ntkFunc = ABC_FUNC_BDD;
    return 1;
}

/**Function*************************************************************

  Synopsis    [Converts the node from SOP to BDD representation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Abc_ConvertSopToBdd( DdManager * dd, char * pSop )
{
    DdNode * bSum, * bCube, * bTemp, * bVar;
    char * pCube;
    int nVars, Value, v;
    extern int Abc_SopIsExorType( char * pSop );

    // start the cover
    nVars = Abc_SopGetVarNum(pSop);
    bSum = Cudd_ReadLogicZero(dd);   Cudd_Ref( bSum );
    if ( Abc_SopIsExorType(pSop) )
    {
        for ( v = 0; v < nVars; v++ )
        {
            bSum  = Cudd_bddXor( dd, bTemp = bSum, Cudd_bddIthVar(dd, v) );   Cudd_Ref( bSum );
            Cudd_RecursiveDeref( dd, bTemp );
        }
    }
    else
    {
        // check the logic function of the node
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
            bSum = Cudd_bddOr( dd, bTemp = bSum, bCube );   
            Cudd_Ref( bSum );
            Cudd_RecursiveDeref( dd, bTemp );
            Cudd_RecursiveDeref( dd, bCube );
        }
    }
    // complement the result if necessary
    bSum = Cudd_NotCond( bSum, !Abc_SopGetPhase(pSop) );
    Cudd_Deref( bSum );
    return bSum;
}

/**Function*************************************************************

  Synopsis    [Removes complemented SOP covers.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NtkLogicMakeDirectSops( Abc_Ntk_t * pNtk )
{
    DdManager * dd;
    DdNode * bFunc;
    Vec_Str_t * vCube;
    Abc_Obj_t * pNode;
    int nFaninsMax, fFound, i;

    assert( Abc_NtkIsSopLogic(pNtk) );

    // check if there are nodes with complemented SOPs
    fFound = 0;
    Abc_NtkForEachNode( pNtk, pNode, i )
        if ( Abc_SopIsComplement(pNode->pData) )
        {
            fFound = 1;
            break;
        }
    if ( !fFound )
        return;

    // start the BDD package
    nFaninsMax = Abc_NtkGetFaninMax( pNtk );
    if ( nFaninsMax == 0 )
        printf( "Warning: The network has only constant nodes.\n" );
    dd = Cudd_Init( nFaninsMax, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0 );

    // change the cover of negated nodes
    vCube = Vec_StrAlloc( 100 );
    Abc_NtkForEachNode( pNtk, pNode, i )
        if ( Abc_SopIsComplement(pNode->pData) )
        {
            bFunc = Abc_ConvertSopToBdd( dd, pNode->pData );  Cudd_Ref( bFunc );
            pNode->pData = Abc_ConvertBddToSop( pNtk->pManFunc, dd, bFunc, bFunc, Abc_ObjFaninNum(pNode), vCube, 1 );
            Cudd_RecursiveDeref( dd, bFunc );
            assert( !Abc_SopIsComplement(pNode->pData) );
        }
    Vec_StrFree( vCube );
    Extra_StopManager( dd );
}





/**Function*************************************************************

  Synopsis    [Converts the network from BDD to SOP representation.]

  Description [If the flag is set to 1, forces the direct phase of all covers.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkBddToSop( Abc_Ntk_t * pNtk, int fDirect )
{
    Abc_Obj_t * pNode;
    Extra_MmFlex_t * pManNew;
    DdManager * dd = pNtk->pManFunc;
    DdNode * bFunc;
    Vec_Str_t * vCube;
    int i, fMode;

    if ( fDirect )
        fMode = 1;
    else
        fMode = -1;

    assert( Abc_NtkIsBddLogic(pNtk) ); 
    Cudd_zddVarsFromBddVars( dd, 2 );
    // create the new manager
    pManNew = Extra_MmFlexStart();

    // go through the objects
    vCube = Vec_StrAlloc( 100 );
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        assert( pNode->pData );
        bFunc = pNode->pData;
        pNode->pNext = (Abc_Obj_t *)Abc_ConvertBddToSop( pManNew, dd, bFunc, bFunc, Abc_ObjFaninNum(pNode), vCube, fMode );
        if ( pNode->pNext == NULL )
        {
            Extra_MmFlexStop( pManNew, 0 );
            Abc_NtkCleanNext( pNtk );
//            printf( "Converting from BDDs to SOPs has failed.\n" );
            Vec_StrFree( vCube );
            return 0;
        }
    }
    Vec_StrFree( vCube );

    // update the network type
    pNtk->ntkFunc = ABC_FUNC_SOP;
    // set the new manager
    pNtk->pManFunc = pManNew;
    // transfer from next to data
    Abc_NtkForEachNode( pNtk, pNode, i )
    {
        Cudd_RecursiveDeref( dd, pNode->pData );
        pNode->pData = pNode->pNext;
        pNode->pNext = NULL;
    }

    // check for remaining references in the package
    Extra_StopManager( dd );
    return 1;
}

/**Function*************************************************************

  Synopsis    [Converts the node from BDD to SOP representation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
char * Abc_ConvertBddToSop( Extra_MmFlex_t * pMan, DdManager * dd, DdNode * bFuncOn, DdNode * bFuncOnDc, int nFanins, Vec_Str_t * vCube, int fMode )
{
    int fVerify = 0;
    char * pSop;
    DdNode * bFuncNew, * bCover, * zCover, * zCover0, * zCover1;
    int nCubes, nCubes0, nCubes1, fPhase;

    assert( bFuncOn == bFuncOnDc || Cudd_bddLeq( dd, bFuncOn, bFuncOnDc ) );
    if ( Cudd_IsConstant(bFuncOn) || Cudd_IsConstant(bFuncOnDc) )
    {
        if ( fMode == -1 ) // if the phase is not known, write constant 1
            fMode = 1;
        Vec_StrFill( vCube, nFanins, '-' );
        Vec_StrPush( vCube, '\0' );
        if ( pMan )
            pSop = Extra_MmFlexEntryFetch( pMan, nFanins + 4 );
        else
            pSop = ALLOC( char, nFanins + 4 );
        if ( bFuncOn == Cudd_ReadOne(dd) )
            sprintf( pSop, "%s %d\n", vCube->pArray, fMode );
        else
            sprintf( pSop, "%s %d\n", vCube->pArray, !fMode );
        return pSop;
    }


    if ( fMode == -1 )
    { // try both phases

        // get the ZDD of the negative polarity
        bCover = Cudd_zddIsop( dd, Cudd_Not(bFuncOnDc), Cudd_Not(bFuncOn), &zCover0 );
        Cudd_Ref( zCover0 );
        Cudd_Ref( bCover );
        Cudd_RecursiveDeref( dd, bCover );
        nCubes0 = Abc_CountZddCubes( dd, zCover0 );

        // get the ZDD of the positive polarity
        bCover = Cudd_zddIsop( dd, bFuncOn, bFuncOnDc, &zCover1 );
        Cudd_Ref( zCover1 );
        Cudd_Ref( bCover );
        Cudd_RecursiveDeref( dd, bCover );
        nCubes1 = Abc_CountZddCubes( dd, zCover1 );

        // compare the number of cubes
        if ( nCubes1 <= nCubes0 )
        { // use positive polarity
            nCubes = nCubes1;
            zCover = zCover1;
            Cudd_RecursiveDerefZdd( dd, zCover0 );
            fPhase = 1;
        }
        else
        { // use negative polarity
            nCubes = nCubes0;
            zCover = zCover0;
            Cudd_RecursiveDerefZdd( dd, zCover1 );
            fPhase = 0;
        }
    }
    else if ( fMode == 0 )
    {
        // get the ZDD of the negative polarity
        bCover = Cudd_zddIsop( dd, Cudd_Not(bFuncOnDc), Cudd_Not(bFuncOn), &zCover );
        Cudd_Ref( zCover );
        Cudd_Ref( bCover );
        Cudd_RecursiveDeref( dd, bCover );
        nCubes = Abc_CountZddCubes( dd, zCover );
        fPhase = 0;
    }
    else if ( fMode == 1 )
    {
        // get the ZDD of the positive polarity
        bCover = Cudd_zddIsop( dd, bFuncOn, bFuncOnDc, &zCover );
        Cudd_Ref( zCover );
        Cudd_Ref( bCover );
        Cudd_RecursiveDeref( dd, bCover );
        nCubes = Abc_CountZddCubes( dd, zCover );
        fPhase = 1;
    }
    else
    {
        assert( 0 );
    }

    if ( nCubes > ABC_MUX_CUBES )
    {
        Cudd_RecursiveDerefZdd( dd, zCover );
        printf( "The number of cubes exceeded the predefined limit (%d).\n", ABC_MUX_CUBES );
        return NULL;
    }

    // allocate memory for the cover
    if ( pMan )
        pSop = Extra_MmFlexEntryFetch( pMan, (nFanins + 3) * nCubes + 1 );
    else 
        pSop = ALLOC( char, (nFanins + 3) * nCubes + 1 );
    pSop[(nFanins + 3) * nCubes] = 0;
    // create the SOP
    Vec_StrFill( vCube, nFanins, '-' );
    Vec_StrPush( vCube, '\0' );
    Abc_ConvertZddToSop( dd, zCover, pSop, nFanins, vCube, fPhase );
    Cudd_RecursiveDerefZdd( dd, zCover );

    // verify
    if ( fVerify )
    {
        bFuncNew = Abc_ConvertSopToBdd( dd, pSop );  Cudd_Ref( bFuncNew );
        if ( bFuncOn == bFuncOnDc )
        {
            if ( bFuncNew != bFuncOn )
                printf( "Verification failed.\n" );
        }
        else
        {
            if ( !Cudd_bddLeq(dd, bFuncOn, bFuncNew) || !Cudd_bddLeq(dd, bFuncNew, bFuncOnDc) )
                printf( "Verification failed.\n" );
        }
        Cudd_RecursiveDeref( dd, bFuncNew );
    }
    return pSop;
}

/**Function*************************************************************

  Synopsis    [Derive the SOP from the ZDD representation of the cubes.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_ConvertZddToSop_rec( DdManager * dd, DdNode * zCover, char * pSop, int nFanins, Vec_Str_t * vCube, int fPhase, int * pnCubes )
{
    DdNode * zC0, * zC1, * zC2;
    int Index;

    if ( zCover == dd->zero )
        return;
    if ( zCover == dd->one )
    {
        char * pCube;
        pCube = pSop + (*pnCubes) * (nFanins + 3);
        sprintf( pCube, "%s %d\n", vCube->pArray, fPhase );
        (*pnCubes)++;
        return;
    }
    Index = zCover->index/2;
    assert( Index < nFanins );
    extraDecomposeCover( dd, zCover, &zC0, &zC1, &zC2 );
    vCube->pArray[Index] = '0';
    Abc_ConvertZddToSop_rec( dd, zC0, pSop, nFanins, vCube, fPhase, pnCubes );
    vCube->pArray[Index] = '1';
    Abc_ConvertZddToSop_rec( dd, zC1, pSop, nFanins, vCube, fPhase, pnCubes );
    vCube->pArray[Index] = '-';
    Abc_ConvertZddToSop_rec( dd, zC2, pSop, nFanins, vCube, fPhase, pnCubes );
}

/**Function*************************************************************

  Synopsis    [Derive the BDD for the function in the cut.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ConvertZddToSop( DdManager * dd, DdNode * zCover, char * pSop, int nFanins, Vec_Str_t * vCube, int fPhase )
{
    int nCubes = 0;
    Abc_ConvertZddToSop_rec( dd, zCover, pSop, nFanins, vCube, fPhase, &nCubes );
    return nCubes;
}


/**Function*************************************************************

  Synopsis    [Computes the SOPs of the negative and positive phase of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_NodeBddToCnf( Abc_Obj_t * pNode, Extra_MmFlex_t * pMmMan, Vec_Str_t * vCube, char ** ppSop0, char ** ppSop1 )
{
    assert( Abc_NtkIsBddLogic(pNode->pNtk) ); 
    *ppSop0 = Abc_ConvertBddToSop( pMmMan, pNode->pNtk->pManFunc, pNode->pData, pNode->pData, Abc_ObjFaninNum(pNode), vCube, 0 );
    *ppSop1 = Abc_ConvertBddToSop( pMmMan, pNode->pNtk->pManFunc, pNode->pData, pNode->pData, Abc_ObjFaninNum(pNode), vCube, 1 );
}




/**Function*************************************************************

  Synopsis    [Count the number of paths in the ZDD.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Abc_CountZddCubes_rec( DdManager * dd, DdNode * zCover, int * pnCubes )
{
    DdNode * zC0, * zC1, * zC2;
    if ( zCover == dd->zero )
        return;
    if ( zCover == dd->one )
    {
        (*pnCubes)++;
        return;
    }
    if ( (*pnCubes) > ABC_MUX_CUBES )
        return;
    extraDecomposeCover( dd, zCover, &zC0, &zC1, &zC2 );
    Abc_CountZddCubes_rec( dd, zC0, pnCubes );
    Abc_CountZddCubes_rec( dd, zC1, pnCubes );
    Abc_CountZddCubes_rec( dd, zC2, pnCubes );
}

/**Function*************************************************************

  Synopsis    [Count the number of paths in the ZDD.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_CountZddCubes( DdManager * dd, DdNode * zCover )
{
    int nCubes = 0;
    Abc_CountZddCubes_rec( dd, zCover, &nCubes );
    return nCubes;
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


